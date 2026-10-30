-- Prove2me | Theorems.Thm_TwoEchelonVRP_theorem_2
-- name    : TwoEchelonVRP.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:37:16.745493+00:00
-- url     : https://prove2.me/theorems/cc0c5b04-b475-4abe-bc01-5daf3ffff3b9
-- title:
--   Theorem 2: $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ge z(LF)$, and the inequality can be strict
-- statement:
--   Let $I$ be an instance of the two-echelon capacitated vehicle routing problem (2E-CVRP): a depot $0$, satellites $N_S$ and customers $N_C$ on the graph $G$ of §2, travel costs satisfying the triangle inequality, demands $q_i$, $m^1$ first-level vehicles of capacity $Q_1$, $m_k$ second-level vehicles of capacity $Q_2 < Q_1$ at satellite $k$, at most $m^2 \le \sum_k m_k$ second-level vehicles in total, satellite capacities $B_k$, handling costs $H_k$ and vehicle fixed costs $U_1, U_2$ folded into the travel costs. Let $z(F)$ be the optimal cost of formulation F (1)–(11), $z(LF)$ that of its LP relaxation, and $z(RF(\beta,\lambda,\mu))$ the value of the Lagrangean relaxation RF (13)–(18) for multipliers $\lambda \in \mathbb R^{N_C}$, $\mu = (\mu_1, \dots, \mu_{n_s}, \mu_0) \in \mathbb R_-^{N_S+1}$ and marginal routing costs $\beta$ solving the inequalities (12).
--
--   **Theorem 2.** The relation $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ge z(LF)$ holds, and such inequality can be strict. Precisely:
--
--   1. for every instance, $\displaystyle \sup_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)) \ \ge\ z(LF)$, the supremum over all $\lambda \in \mathbb R^{N_C}$, $\mu \in \mathbb R_-^{N_S+1}$ and $\beta$ solving (12);
--   2. for every instance in which the supremum is not $+\infty$ (in particular every instance in which F has a feasible solution), the supremum is attained by some admissible $(\beta, \lambda, \mu)$, so it is a maximum;
--   3. there is an instance, with nonnegative travel costs, fixed costs, handling costs and satellite capacities and positive demands, in which F has a feasible solution and the inequality is strict.
--
--   The Lagrangean relaxation RF, which the paper's dynamic-programming bounding procedure solves, is therefore at least as strong as the LP relaxation of the set-partitioning formulation F, and sometimes stronger.
--
--   **Formalization Note** Values are extended reals ($+\infty$ for an infeasible problem), so clause 1 holds for every instance; clause 2 makes the paper's "max" precise wherever it is a number.
--
--   Differences from the source:
--   - generalization: z(F), z(LF), z(RF(β, λ, μ)) as optimal costs (real numbers) of feasible problems → EReal infima of the objective values, +∞ when the problem is infeasible; the statement holds for every instance; reason: where the problems are feasible these are the paper's real optima, so the statement specializes to the paper's
--   - reading: max_{β,λ,μ}{z(RF(β, λ, μ))} → the EReal supremum rfSup over admissible (β, λ, μ); attainment is asserted separately (theorem_2_max_attained) whenever rfSup ≠ +∞; reason: the supremum can be +∞ and is then not attained, so a maximum exists exactly where the paper's max is a number
--   - reading: 'max' in max_{β,λ,μ}{z(RF(β, λ, μ))} → whenever rfSup ≠ +∞, some admissible (β, λ, μ) attains the supremum rfSup; reason: the supremum can be +∞ and is then unattained; the hypothesis rfSup ≠ +∞ says exactly that the paper's maximum is a number (it holds whenever F has a feasible solution)
--   - reading: 'such inequality can be strict' → there is an instance satisfying every standing assumption, with nonnegative costs, fixed costs, handling costs and satellite capacities and positive demands, in which F has a feasible solution and z(LF) < rfSup; reason: the extra conjuncts make the existential stronger: they rule out a witness whose right-hand side is +∞ because RF is infeasible, and a witness outside the usual 2E-CVRP data
--   - reading: LF, 'the LP-relaxation of formulation F' → (2)-(8) with 0 ≤ x ≤ 1, 0 ≤ y ≤ 1, q ≥ 0 real; reason: the standard LP relaxation of binary and nonnegative-integer variables
--   - reading: second-level route: 'a simple cycle in G passing through a satellite and a subset of customers' → nonempty injective customer sequence in canonical orientation (one index per cycle), single-customer cycles (k, i, k) included; reason: the paper's algorithm starts from 'all single-customer routes (k, i, k)' (§4.1, p. 302)
--   - reading: route cost 'the sum of the costs of the traversed edges' (g_r, c_kl) → edges summed along the cycle, so (0, k, 0) costs 2 d'_0k and (k, i, k) costs 2 d'_ki; reason: with each edge counted once, (0, k, 0) would carry only U_1/2 of the fixed cost U_1 that the modification (i)-(ii) of p. 299 is meant to charge
--   - reading: 'matrix d_ij satisfies the triangle inequality', d defined on E → d_uw ≤ d_uv + d_vw for every triangle {u, v, w} of G; d symmetric on edges; reason: d is defined only on the edges of G; on G this is equivalent to d_uw ≤ the cost of every u-w path
--   - reading: demands q_i ('units of goods'), capacities Q_1, Q_2 and vehicle numbers m^1, m_k, m^2 → natural numbers; reason: goods are counted in units: deliveries q_kr are integers (11) and the load sets W_r ⊆ ℤ₊ (p. 299) are bounded by Q_1; vehicle numbers are counts
--   - generalization: costs d_ij, U_1, U_2, H_k and capacities B_k of a 2E-CVRP instance (no sign stated) → arbitrary real numbers; reason: covers every instance with nonnegative data, so the universally quantified statement specializes to it
--   - encoding: N_S = {1..n_s}, N_C = {n_s+1..n_s+n_c}, depot 0; variables x_kl, y_r, q_kr, ξ_ik → Fin ns, Fin nc (0-based), vertices Option (Fin ns ⊕ Fin nc); real-valued variables with integrality predicates; reason: Lean convention; same instances and the same feasible sets
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, Theorem 2, p. 301

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_zF
import Definitions.Def_TwoEchelonVRP_zLF
import Definitions.Def_TwoEchelonVRP_MultFeasible
import Definitions.Def_TwoEchelonVRP_zRF
import Definitions.Def_TwoEchelonVRP_rfSup

namespace TwoEchelonVRP

/-- **Theorem 2 (Baldacci, Mingozzi, Roberti & Wolfler Calvo 2013): the best Lagrangean bound RF
dominates the LP-relaxation bound, sometimes strictly.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, Theorem 2, p. 301: "The relation
max_{β,λ,μ}{z(RF(β, λ, μ))} ≥ z(LF) holds, and such inequality can be strict."

Three clauses:
* (a) for every 2E-CVRP instance, `z(LF) ≤ sup_{β,λ,μ} z(RF(β, λ, μ))`, the supremum over all
  `β` solving (12), `λ ∈ ℝ^{N_C}` and `μ ∈ ℝ_−^{N_S+1}`;
* (b) whenever this supremum is not `+∞`, it is attained (it is a maximum); this covers every
  instance in which formulation F has a feasible solution;
* (c) there is an instance, with nonnegative costs and satellite capacities and positive demands,
  in which F has a feasible solution and the inequality is strict.

**Formalization Note.** Values are `EReal` infima/suprema (`+∞` on an infeasible problem), so (a)
holds for every instance. The paper's "max" is attainment, asserted in (b) wherever the supremum is
a number; the supremum can be `+∞` and then has no maximizer. `Instance` assumes no sign on costs and capacities,
so (a) and (b) cover every sign; the witness of (c) is required to be nonnegative. Second-level routes are the canonical, elementary,
nonempty customer sequences (single-customer routes included); first-level routes are the canonical
satellite sequences, with `⌈min{m_k Q_2, q_tot}/Q_1⌉` copies of each `(0, k, 0)`. LF relaxes
(9)–(11) to `0 ≤ x ≤ 1`, `0 ≤ y ≤ 1`, `q ≥ 0`. -/
theorem theorem_2 :
    (∀ (ns nc : ℕ) (I : Instance ns nc), zLF I ≤ rfSup I) ∧
    (∀ (ns nc : ℕ) (I : Instance ns nc), rfSup I ≠ ⊤ →
      ∃ β lam μ μ0, MultFeasible I β lam μ μ0 ∧ zRF I β lam μ μ0 = rfSup I) ∧
    (∃ (ns nc : ℕ) (I : Instance ns nc),
      ((∀ u v, IsEdge u v → 0 ≤ I.d u v) ∧ 0 ≤ I.U1 ∧ 0 ≤ I.U2 ∧ (∀ k, 0 ≤ I.H k) ∧
        (∀ k, 0 ≤ I.B k) ∧ (∀ i, 0 < I.q i)) ∧
      (∃ x y qd, FFeasible I x y qd) ∧ zLF I < rfSup I) := by sorry

end TwoEchelonVRP
