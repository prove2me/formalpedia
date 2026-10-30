-- Prove2me | Theorems.Thm_TwoEchelonVRP_theorem_2_max_attained
-- name    : TwoEchelonVRP.theorem_2_max_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:57.981834+00:00
-- url     : https://prove2.me/theorems/6f1b3762-85a6-4aed-a8c8-8959737a1417
-- title:
--   Theorem 2 (the maximum): $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu))$ is attained
-- statement:
--   Let $I$ be an instance of the two-echelon capacitated vehicle routing problem (2E-CVRP): a depot $0$, satellites $N_S$ and customers $N_C$ on the graph $G$ of §2, travel costs satisfying the triangle inequality, demands $q_i$, $m^1$ first-level vehicles of capacity $Q_1$, $m_k$ second-level vehicles of capacity $Q_2 < Q_1$ at satellite $k$, at most $m^2 \le \sum_k m_k$ second-level vehicles in total, satellite capacities $B_k$, handling costs $H_k$ and vehicle fixed costs $U_1, U_2$ folded into the travel costs. Let $z(F)$ be the optimal cost of formulation F (1)–(11), $z(LF)$ that of its LP relaxation, and $z(RF(\beta,\lambda,\mu))$ the value of the Lagrangean relaxation RF (13)–(18) for multipliers $\lambda \in \mathbb R^{N_C}$, $\mu = (\mu_1, \dots, \mu_{n_s}, \mu_0) \in \mathbb R_-^{N_S+1}$ and marginal routing costs $\beta$ solving the inequalities (12).
--
--   **Theorem 2, the maximum.** If $\sup_{\beta',\lambda',\mu'} z(RF(\beta',\lambda',\mu')) < +\infty$ (which holds in particular whenever formulation F has a feasible solution, by Theorem 1), there are $\lambda \in \mathbb R^{N_C}$, $\mu \in \mathbb R_-^{N_S+1}$ and $\beta$ solving (12) with
--
--   $$
--   z(RF(\beta,\lambda,\mu)) = \sup_{\beta',\lambda',\mu'} z(RF(\beta',\lambda',\mu')),
--   $$
--
--   so the bound $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu))$ of Theorem 2 is a maximum. This is clause (b) of the mission's goal `TwoEchelonVRP.theorem_2`.
--
--   **Formalization Note** Values are extended reals. The supremum can be $+\infty$ (for example when some customer lies on no route) and is then not attained; the hypothesis excludes exactly that case.
--
--   Differences from the source:
--   - generalization: z(F), z(LF), z(RF(β, λ, μ)) as optimal costs (real numbers) of feasible problems → EReal infima of the objective values, +∞ when the problem is infeasible; the statement holds for every instance; reason: where the problems are feasible these are the paper's real optima, so the statement specializes to the paper's
--   - reading: 'max' in max_{β,λ,μ}{z(RF(β, λ, μ))} → whenever rfSup ≠ +∞, some admissible (β, λ, μ) attains the supremum rfSup; reason: the supremum can be +∞ and is then unattained; the hypothesis rfSup ≠ +∞ says exactly that the paper's maximum is a number (it holds whenever F has a feasible solution)
--   - reading: second-level route: 'a simple cycle in G passing through a satellite and a subset of customers' → nonempty injective customer sequence in canonical orientation (one index per cycle), single-customer cycles (k, i, k) included; reason: the paper's algorithm starts from 'all single-customer routes (k, i, k)' (§4.1, p. 302)
--   - reading: route cost 'the sum of the costs of the traversed edges' (g_r, c_kl) → edges summed along the cycle, so (0, k, 0) costs 2 d'_0k and (k, i, k) costs 2 d'_ki; reason: with each edge counted once, (0, k, 0) would carry only U_1/2 of the fixed cost U_1 that the modification (i)-(ii) of p. 299 is meant to charge
--   - reading: 'matrix d_ij satisfies the triangle inequality', d defined on E → d_uw ≤ d_uv + d_vw for every triangle {u, v, w} of G; d symmetric on edges; reason: d is defined only on the edges of G; on G this is equivalent to d_uw ≤ the cost of every u-w path
--   - reading: demands q_i ('units of goods'), capacities Q_1, Q_2 and vehicle numbers m^1, m_k, m^2 → natural numbers; reason: goods are counted in units: deliveries q_kr are integers (11) and the load sets W_r ⊆ ℤ₊ (p. 299) are bounded by Q_1; vehicle numbers are counts
--   - generalization: costs d_ij, U_1, U_2, H_k and capacities B_k of a 2E-CVRP instance (no sign stated) → arbitrary real numbers; reason: covers every instance with nonnegative data, so the universally quantified statement specializes to it
--   - encoding: N_S = {1..n_s}, N_C = {n_s+1..n_s+n_c}, depot 0; variables x_kl, y_r, q_kr, ξ_ik → Fin ns, Fin nc (0-based), vertices Option (Fin ns ⊕ Fin nc); real-valued variables with integrality predicates; reason: Lean convention; same instances and the same feasible sets
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, Theorem 2, p. 301 ('max_{β,λ,μ}{z(RF(β, λ, μ))}')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_MultFeasible
import Definitions.Def_TwoEchelonVRP_zRF
import Definitions.Def_TwoEchelonVRP_rfSup

namespace TwoEchelonVRP

/-- **Theorem 2, the maximum: the best RF bound is attained whenever it is finite.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, Theorem 2, p. 301: the bound
"max_{β,λ,μ}{z(RF(β, λ, μ))}" of Theorem 2 is a maximum.

For every 2E-CVRP instance in which the supremum `sup_{β',λ',μ'} z(RF(β', λ', μ'))` is not `+∞`,
there are admissible multipliers `(β, λ, μ)` attaining it.

**Formalization Note.** Clause (b) of `theorem_2`. The paper's "max" is a number; the supremum can
be `+∞` and unattained (for example when some customer lies on no route, so that `β_ik` is
unbounded), and the hypothesis `rfSup I ≠ ⊤` excludes exactly that case. It holds in particular
whenever F has a feasible solution, since then `rfSup I ≤ z(F) < ⊤` by Theorem 1. -/
theorem theorem_2_max_attained {ns nc : ℕ} (I : Instance ns nc)
    (hfin : rfSup I ≠ ⊤) :
    ∃ β lam μ μ0, MultFeasible I β lam μ μ0 ∧ zRF I β lam μ μ0 = rfSup I := by sorry

end TwoEchelonVRP
