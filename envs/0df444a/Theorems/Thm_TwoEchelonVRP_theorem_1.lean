-- Prove2me | Theorems.Thm_TwoEchelonVRP_theorem_1
-- name    : TwoEchelonVRP.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:32:53.024487+00:00
-- url     : https://prove2.me/theorems/bbaf6e3a-17f6-4538-90c8-6b64317b9bfe
-- title:
--   Theorem 1: $z(RF(\beta,\lambda,\mu))$ is a valid lower bound on the 2E-CVRP
-- statement:
--   Let $I$ be an instance of the two-echelon capacitated vehicle routing problem (2E-CVRP): a depot $0$, satellites $N_S$ and customers $N_C$ on the graph $G$ of §2, travel costs satisfying the triangle inequality, demands $q_i$, $m^1$ first-level vehicles of capacity $Q_1$, $m_k$ second-level vehicles of capacity $Q_2 < Q_1$ at satellite $k$, at most $m^2 \le \sum_k m_k$ second-level vehicles in total, satellite capacities $B_k$, handling costs $H_k$ and vehicle fixed costs $U_1, U_2$ folded into the travel costs. Let $z(F)$ be the optimal cost of formulation F (1)–(11), $z(LF)$ that of its LP relaxation, and $z(RF(\beta,\lambda,\mu))$ the value of the Lagrangean relaxation RF (13)–(18) for multipliers $\lambda \in \mathbb R^{N_C}$, $\mu = (\mu_1, \dots, \mu_{n_s}, \mu_0) \in \mathbb R_-^{N_S+1}$ and marginal routing costs $\beta$ solving the inequalities (12).
--
--   **Theorem 1.** For every solution $\beta$ of (12) and all penalty vectors $\lambda \in \mathbb R^{N_C}$, $\mu \in \mathbb R_-^{N_S+1}$,
--
--   $$
--   z(RF(\beta,\lambda,\mu)) \le z(F).
--   $$
--
--   Every admissible choice of multipliers therefore yields a lower bound on the optimal 2E-CVRP cost; the paper's bounding procedure and its route-elimination rule (Corollary 1) rest on it, and it gives the attainment clause of Theorem 2 its upper bound.
--
--   **Formalization Note** Values are extended reals: $z(F) = +\infty$ when F is infeasible, in which case the inequality is trivial.
--
--   Differences from the source:
--   - generalization: z(F), z(LF), z(RF(β, λ, μ)) as optimal costs (real numbers) of feasible problems → EReal infima of the objective values, +∞ when the problem is infeasible; the statement holds for every instance; reason: where the problems are feasible these are the paper's real optima, so the statement specializes to the paper's
--   - reading: 'a valid lower bound on the 2E-CVRP' → zRF I β lam μ μ0 ≤ zF I, z(F) the optimal value of formulation F; reason: F is the paper's formulation of the 2E-CVRP (p. 300); its optimum is the 2E-CVRP optimum
--   - reading: second-level route: 'a simple cycle in G passing through a satellite and a subset of customers' → nonempty injective customer sequence in canonical orientation (one index per cycle), single-customer cycles (k, i, k) included; reason: the paper's algorithm starts from 'all single-customer routes (k, i, k)' (§4.1, p. 302)
--   - reading: route cost 'the sum of the costs of the traversed edges' (g_r, c_kl) → edges summed along the cycle, so (0, k, 0) costs 2 d'_0k and (k, i, k) costs 2 d'_ki; reason: with each edge counted once, (0, k, 0) would carry only U_1/2 of the fixed cost U_1 that the modification (i)-(ii) of p. 299 is meant to charge
--   - reading: 'matrix d_ij satisfies the triangle inequality', d defined on E → d_uw ≤ d_uv + d_vw for every triangle {u, v, w} of G; d symmetric on edges; reason: d is defined only on the edges of G; on G this is equivalent to d_uw ≤ the cost of every u-w path
--   - reading: demands q_i ('units of goods'), capacities Q_1, Q_2 and vehicle numbers m^1, m_k, m^2 → natural numbers; reason: goods are counted in units: deliveries q_kr are integers (11) and the load sets W_r ⊆ ℤ₊ (p. 299) are bounded by Q_1; vehicle numbers are counts
--   - generalization: costs d_ij, U_1, U_2, H_k and capacities B_k of a 2E-CVRP instance (no sign stated) → arbitrary real numbers; reason: covers every instance with nonnegative data, so the universally quantified statement specializes to it
--   - encoding: N_S = {1..n_s}, N_C = {n_s+1..n_s+n_c}, depot 0; variables x_kl, y_r, q_kr, ξ_ik → Fin ns, Fin nc (0-based), vertices Option (Fin ns ⊕ Fin nc); real-valued variables with integrality predicates; reason: Lean convention; same instances and the same feasible sets
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, Theorem 1, p. 301

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_zF
import Definitions.Def_TwoEchelonVRP_MultFeasible
import Definitions.Def_TwoEchelonVRP_zRF

namespace TwoEchelonVRP

/-- **Theorem 1 (Baldacci, Mingozzi, Roberti & Wolfler Calvo 2013): RF is a valid lower bound.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, Theorem 1, p. 301: "z(RF(β, λ, μ)) is a valid
lower bound on the 2E-CVRP for any solution β of inequalities (12) and any pair of penalty vectors
λ ∈ ℝ^{N_C} and μ ∈ ℝ_−^{N_S+1}."

For every 2E-CVRP instance and all multipliers satisfying `μ_k ≤ 0`, `μ_0 ≤ 0` and (12),
`z(RF(β, λ, μ)) ≤ z(F)`.

**Formalization Note.** `z(F)` and `z(RF)` are `EReal` infima, `+∞` on an empty feasible set; when F
is infeasible the inequality is trivial. Second-level routes are the canonical, elementary,
nonempty customer sequences of `Route2` (single-customer routes included). -/
theorem theorem_1 {ns nc : ℕ} (I : Instance ns nc) (β : Fin nc → Fin ns → ℝ) (lam : Fin nc → ℝ)
    (μ : Fin ns → ℝ) (μ0 : ℝ) (h : MultFeasible I β lam μ μ0) :
    zRF I β lam μ μ0 ≤ zF I := by sorry

end TwoEchelonVRP
