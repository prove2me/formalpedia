-- Prove2me | Theorems.Thm_TwoEchelonVRP_theorem_2_strict
-- name    : TwoEchelonVRP.theorem_2_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:35:57.857323+00:00
-- url     : https://prove2.me/theorems/b9eaa28a-1af9-4426-b295-477ca69f3592
-- title:
--   Theorem 2 (strictness): the inequality $\max_{\beta,\lambda,\mu} z(RF) \ge z(LF)$ can be strict
-- statement:
--   Let $I$ be an instance of the two-echelon capacitated vehicle routing problem (2E-CVRP): a depot $0$, satellites $N_S$ and customers $N_C$ on the graph $G$ of §2, travel costs satisfying the triangle inequality, demands $q_i$, $m^1$ first-level vehicles of capacity $Q_1$, $m_k$ second-level vehicles of capacity $Q_2 < Q_1$ at satellite $k$, at most $m^2 \le \sum_k m_k$ second-level vehicles in total, satellite capacities $B_k$, handling costs $H_k$ and vehicle fixed costs $U_1, U_2$ folded into the travel costs. Let $z(F)$ be the optimal cost of formulation F (1)–(11), $z(LF)$ that of its LP relaxation, and $z(RF(\beta,\lambda,\mu))$ the value of the Lagrangean relaxation RF (13)–(18) for multipliers $\lambda \in \mathbb R^{N_C}$, $\mu = (\mu_1, \dots, \mu_{n_s}, \mu_0) \in \mathbb R_-^{N_S+1}$ and marginal routing costs $\beta$ solving the inequalities (12).
--
--   **Theorem 2, second part.** The inequality can be strict: there is an instance, with nonnegative travel costs, fixed costs, handling costs and satellite capacities and positive demands, in which formulation F has a feasible solution and
--
--   $$
--   z(LF) \ <\ \sup_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu)).
--   $$
--
--   So relaxation RF can give a strictly better lower bound than the LP relaxation. This is clause (c) of the mission's goal `TwoEchelonVRP.theorem_2`.
--
--   **Formalization Note** The witness must satisfy every field of the instance (triangle inequality, $Q_2 < Q_1$, $m^2 \le \sum_k m_k$) and admit a feasible solution of F, which rules out a witness whose right-hand side is $+\infty$ only because RF is infeasible.
--
--   Differences from the source:
--   - generalization: z(F), z(LF), z(RF(β, λ, μ)) as optimal costs (real numbers) of feasible problems → EReal infima of the objective values, +∞ when the problem is infeasible; the statement holds for every instance; reason: where the problems are feasible these are the paper's real optima, so the statement specializes to the paper's
--   - reading: 'such inequality can be strict' → there is an instance satisfying every standing assumption, with nonnegative costs, fixed costs, handling costs and satellite capacities and positive demands, in which F has a feasible solution and z(LF) < rfSup; reason: the extra conjuncts make the existential stronger: they rule out a witness whose right-hand side is +∞ because RF is infeasible, and a witness outside the usual 2E-CVRP data
--   - reading: LF, 'the LP-relaxation of formulation F' → (2)-(8) with 0 ≤ x ≤ 1, 0 ≤ y ≤ 1, q ≥ 0 real; reason: the standard LP relaxation of binary and nonnegative-integer variables
--   - reading: second-level route: 'a simple cycle in G passing through a satellite and a subset of customers' → nonempty injective customer sequence in canonical orientation (one index per cycle), single-customer cycles (k, i, k) included; reason: the paper's algorithm starts from 'all single-customer routes (k, i, k)' (§4.1, p. 302)
--   - reading: route cost 'the sum of the costs of the traversed edges' (g_r, c_kl) → edges summed along the cycle, so (0, k, 0) costs 2 d'_0k and (k, i, k) costs 2 d'_ki; reason: with each edge counted once, (0, k, 0) would carry only U_1/2 of the fixed cost U_1 that the modification (i)-(ii) of p. 299 is meant to charge
--   - reading: 'matrix d_ij satisfies the triangle inequality', d defined on E → d_uw ≤ d_uv + d_vw for every triangle {u, v, w} of G; d symmetric on edges; reason: d is defined only on the edges of G; on G this is equivalent to d_uw ≤ the cost of every u-w path
--   - reading: demands q_i ('units of goods'), capacities Q_1, Q_2 and vehicle numbers m^1, m_k, m^2 → natural numbers; reason: goods are counted in units: deliveries q_kr are integers (11) and the load sets W_r ⊆ ℤ₊ (p. 299) are bounded by Q_1; vehicle numbers are counts
--   - generalization: costs d_ij, U_1, U_2, H_k and capacities B_k of a 2E-CVRP instance (no sign stated) → arbitrary real numbers; reason: covers every instance with nonnegative data, so the universally quantified statement specializes to it
--   - encoding: N_S = {1..n_s}, N_C = {n_s+1..n_s+n_c}, depot 0; variables x_kl, y_r, q_kr, ξ_ik → Fin ns, Fin nc (0-based), vertices Option (Fin ns ⊕ Fin nc); real-valued variables with integrality predicates; reason: Lean convention; same instances and the same feasible sets
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, Theorem 2, p. 301 ('and such inequality can be strict')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_zF
import Definitions.Def_TwoEchelonVRP_zLF
import Definitions.Def_TwoEchelonVRP_rfSup

namespace TwoEchelonVRP

/-- **Theorem 2, strictness: the best RF bound can exceed the LP-relaxation bound.**
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, Theorem 2, p. 301: "and such inequality can be
strict."

There is a 2E-CVRP instance (satisfying every standing assumption of §2: triangle inequality,
`Q_2 < Q_1`, `m² ≤ Σ_k m_k`), with nonnegative travel costs, fixed costs, handling costs and
satellite capacities and positive demands, in which formulation F has a feasible solution and
`z(LF) < sup_{β,λ,μ} z(RF(β, λ, μ))`.

**Formalization Note.** Clause (c) of `theorem_2`. Requiring a feasible solution of F excludes
witnesses in which RF is infeasible and the right-hand side is `+∞` for free. The sign conditions
make the witness an instance of the 2E-CVRP in its usual sense (costs and capacities nonnegative,
every customer with a positive demand), although `Instance` itself assumes no sign. -/
theorem theorem_2_strict :
    ∃ (ns nc : ℕ) (I : Instance ns nc),
      ((∀ u v, IsEdge u v → 0 ≤ I.d u v) ∧ 0 ≤ I.U1 ∧ 0 ≤ I.U2 ∧ (∀ k, 0 ≤ I.H k) ∧
        (∀ k, 0 ≤ I.B k) ∧ (∀ i, 0 < I.q i)) ∧
      (∃ x y qd, FFeasible I x y qd) ∧ zLF I < rfSup I := by sorry

end TwoEchelonVRP
