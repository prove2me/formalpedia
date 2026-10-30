-- Prove2me | Theorems.Thm_TwoEchelonVRP_theorem_2_inequality
-- name    : TwoEchelonVRP.theorem_2_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:33:55.26822+00:00
-- url     : https://prove2.me/theorems/31bbea1c-f7ad-4d92-9764-53f503d39ad3
-- title:
--   Theorem 2 (inequality): $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ge z(LF)$
-- statement:
--   Let $I$ be an instance of the two-echelon capacitated vehicle routing problem (2E-CVRP): a depot $0$, satellites $N_S$ and customers $N_C$ on the graph $G$ of §2, travel costs satisfying the triangle inequality, demands $q_i$, $m^1$ first-level vehicles of capacity $Q_1$, $m_k$ second-level vehicles of capacity $Q_2 < Q_1$ at satellite $k$, at most $m^2 \le \sum_k m_k$ second-level vehicles in total, satellite capacities $B_k$, handling costs $H_k$ and vehicle fixed costs $U_1, U_2$ folded into the travel costs. Let $z(F)$ be the optimal cost of formulation F (1)–(11), $z(LF)$ that of its LP relaxation, and $z(RF(\beta,\lambda,\mu))$ the value of the Lagrangean relaxation RF (13)–(18) for multipliers $\lambda \in \mathbb R^{N_C}$, $\mu = (\mu_1, \dots, \mu_{n_s}, \mu_0) \in \mathbb R_-^{N_S+1}$ and marginal routing costs $\beta$ solving the inequalities (12).
--
--   **Theorem 2, first part.** For every instance,
--
--   $$
--   \sup_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ \ge\ z(LF),
--   $$
--
--   the supremum taken over all $\lambda \in \mathbb R^{N_C}$, $\mu \in \mathbb R_-^{N_S+1}$ and $\beta$ solving (12).
--
--   The best Lagrangean bound is thus never weaker than the LP-relaxation bound; this is clause (a) of the mission's goal `TwoEchelonVRP.theorem_2`. That the supremum is a maximum is `TwoEchelonVRP.theorem_2_max_attained`, and that the inequality can be strict is `TwoEchelonVRP.theorem_2_strict`.
--
--   **Formalization Note** Values are extended reals: $z(LF) = +\infty$ when LF is infeasible, and the statement holds for every instance.
--
--   Differences from the source:
--   - generalization: z(F), z(LF), z(RF(β, λ, μ)) as optimal costs (real numbers) of feasible problems → EReal infima of the objective values, +∞ when the problem is infeasible; the statement holds for every instance; reason: where the problems are feasible these are the paper's real optima, so the statement specializes to the paper's
--   - reading: max_{β,λ,μ}{z(RF(β, λ, μ))} → the EReal supremum rfSup over admissible (β, λ, μ); attainment is asserted separately (theorem_2_max_attained) whenever rfSup ≠ +∞; reason: the supremum can be +∞ and is then not attained, so a maximum exists exactly where the paper's max is a number
--   - reading: LF, 'the LP-relaxation of formulation F' → (2)-(8) with 0 ≤ x ≤ 1, 0 ≤ y ≤ 1, q ≥ 0 real; reason: the standard LP relaxation of binary and nonnegative-integer variables
--   - reading: second-level route: 'a simple cycle in G passing through a satellite and a subset of customers' → nonempty injective customer sequence in canonical orientation (one index per cycle), single-customer cycles (k, i, k) included; reason: the paper's algorithm starts from 'all single-customer routes (k, i, k)' (§4.1, p. 302)
--   - reading: route cost 'the sum of the costs of the traversed edges' (g_r, c_kl) → edges summed along the cycle, so (0, k, 0) costs 2 d'_0k and (k, i, k) costs 2 d'_ki; reason: with each edge counted once, (0, k, 0) would carry only U_1/2 of the fixed cost U_1 that the modification (i)-(ii) of p. 299 is meant to charge
--   - reading: 'matrix d_ij satisfies the triangle inequality', d defined on E → d_uw ≤ d_uv + d_vw for every triangle {u, v, w} of G; d symmetric on edges; reason: d is defined only on the edges of G; on G this is equivalent to d_uw ≤ the cost of every u-w path
--   - reading: demands q_i ('units of goods'), capacities Q_1, Q_2 and vehicle numbers m^1, m_k, m^2 → natural numbers; reason: goods are counted in units: deliveries q_kr are integers (11) and the load sets W_r ⊆ ℤ₊ (p. 299) are bounded by Q_1; vehicle numbers are counts
--   - generalization: costs d_ij, U_1, U_2, H_k and capacities B_k of a 2E-CVRP instance (no sign stated) → arbitrary real numbers; reason: covers every instance with nonnegative data, so the universally quantified statement specializes to it
--   - encoding: N_S = {1..n_s}, N_C = {n_s+1..n_s+n_c}, depot 0; variables x_kl, y_r, q_kr, ξ_ik → Fin ns, Fin nc (0-based), vertices Option (Fin ns ⊕ Fin nc); real-valued variables with integrality predicates; reason: Lean convention; same instances and the same feasible sets
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, Theorem 2, p. 301 ('The relation max_{β,λ,μ}{z(RF(β, λ, μ))} ≥ z(LF) holds')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_zLF
import Definitions.Def_TwoEchelonVRP_rfSup

namespace TwoEchelonVRP

/-- **Theorem 2, the inequality: the best RF bound is at least the LP-relaxation bound.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, Theorem 2, p. 301: "The relation
max_{β,λ,μ}{z(RF(β, λ, μ))} ≥ z(LF) holds".

For every 2E-CVRP instance, `z(LF) ≤ sup { z(RF(β, λ, μ)) : (β, λ, μ) admissible }`.

**Formalization Note.** Clause (a) of `theorem_2`. All values are `EReal`: `z(LF) = +∞` when LF is
infeasible, and the supremum is taken in `EReal`. The inequality is stated for every instance,
feasible or not. Attainment of the maximum is `theorem_2_max_attained`. -/
theorem theorem_2_inequality {ns nc : ℕ} (I : Instance ns nc) : zLF I ≤ rfSup I := by sorry

end TwoEchelonVRP
