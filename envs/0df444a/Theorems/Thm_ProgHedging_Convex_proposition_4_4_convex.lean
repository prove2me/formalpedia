-- Prove2me | Theorems.Thm_ProgHedging_Convex_proposition_4_4_convex
-- name    : ProgHedging.Convex.proposition_4_4_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:10.857657+00:00
-- url     : https://prove2.me/theorems/ed974546-00f5-44f4-9af8-74118a7cfe1f
-- title:
--   Proposition 4.4 (convex case) — local optimality for (P^ν) implies the scenario-wise subgradient conditions, which characterize the unique solution of (P^ν) and of each (P^ν_s)
-- statement:
--   Assume the convex case and let $r>0$, $V$ (playing $\hat X^\nu$) and $W$ (playing $W^\nu$) be policies. Write $F^\nu(X)=F(X)+\langle X,W\rangle+\tfrac12 r\|X-V\|^2$ for the objective of the subproblem $(P^\nu)$ over $\mathcal C$.
--
--   1. If a policy $X^+\in\mathcal C$ is locally optimal for $F^\nu$ over $\mathcal C$ (no feasible point near $X^+$ has a smaller value), then for all $s\in S$
--   $$
--   X^+(s)\in C_s,\qquad -W(s)-r\,[X^+(s)-V(s)]\in\partial f_s(X^+(s))+N_{C_s}(X^+(s)).
--   $$
--   2. Conversely, if a policy $X^+$ satisfies these conditions for all $s\in S$, then $X^+$ is the unique global minimizer of $F^\nu$ over $\mathcal C$.
--   3. For each scenario $s$, a point $x$ satisfies $x\in C_s$ and $-W(s)-r[x-V(s)]\in\partial f_s(x)+N_{C_s}(x)$ if and only if $x$ is an optimal solution of $(P^\nu_s)$: minimize $f_s(x)+x\cdot W(s)+\tfrac12r|x-V(s)|^2$ over $C_s$.
--
--   This is the convex-case content of Proposition 4.4, used in the proof of Theorem 5.1 at (5.19)–(5.21).
--
--   Here $\partial f_s$ is the subgradient set of convex analysis and $N_{C_s}$ the normal cone of convex analysis; in the convex case these are Clarke's generalized gradients and normal cones, in which the paper states the first sentence (p. 14).
--
--   **Formalization Note.** Only the convex case is posed: outside it, the first sentence of Proposition 4.4 needs Clarke's generalized gradients and normal cones, which this mission does not define. In item 1 the equivalence (4.17) ⇔ (4.18)–(4.19) is used to state the conclusion directly in the scenario-wise form. Local optimality is with respect to the product topology on policies, which is the topology of the norm (2.3). The statement is proved for arbitrary policies $V,W$; the paper applies it with $V=\hat X^\nu\in\mathcal N$, $W=W^\nu\in\mathcal M$. $\|\cdot\|$ is the norm $\langle X,X\rangle^{1/2}$ (2.3).
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 17, Proposition 4.4 (in the convex case), (4.17)–(4.19)

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ProgHedging_Convex_Duality
open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proposition 4.4, p. 17, in the convex case. Let `r > 0` and data `V = X̂^ν`, `W = W^ν`. A
policy `X⁺` that is locally optimal over `𝒞` for the objective `F(X) + ⟨X, W⟩ + ½ r ‖X − V‖²` of
`(P^ν)` satisfies (4.18)–(4.19), i.e. `X⁺(s) ∈ C_s` and
`−W(s) − r[X⁺(s) − V(s)] ∈ ∂f_s(X⁺(s)) + N_{C_s}(X⁺(s))` for all `s` (in the convex case Clarke's
`∂f_s` and `N_{C_s}` are the subgradient set and the normal cone of convex analysis, p. 14).
Conversely, if `X⁺` satisfies (4.18)–(4.19), then `X⁺` is the unique global minimizer of that
objective over `𝒞`; and for each `s` the same conditions characterize the optimal solutions of
`(P^ν_s)`. -/
theorem proposition_4_4_convex {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (hconv : pr.ConvexCase) {r : ℝ} (hr : 0 < r) (V W : Policy S n) :
    (∀ Xp ∈ pr.adm,
      IsLocalMinOn (fun X => pr.F X + pr.ip X W + r / 2 * pr.pnorm (X - V) ^ 2) pr.adm Xp →
      ∀ s, -(W s) - r • (Xp s - V s) ∈ subdiff (pr.f s) (Xp s) +
        FirstOrderOpt.ConvexTheory.normalCone (pr.C s) (Xp s)) ∧
    (∀ Xp : Policy S n,
      (∀ s, Xp s ∈ pr.C s ∧ -(W s) - r • (Xp s - V s) ∈ subdiff (pr.f s) (Xp s) +
        FirstOrderOpt.ConvexTheory.normalCone (pr.C s) (Xp s)) →
      Xp ∈ pr.adm ∧
      (∀ X ∈ pr.adm, pr.F Xp + pr.ip Xp W + r / 2 * pr.pnorm (Xp - V) ^ 2 ≤
        pr.F X + pr.ip X W + r / 2 * pr.pnorm (X - V) ^ 2) ∧
      ∀ Y ∈ pr.adm, (∀ X ∈ pr.adm, pr.F Y + pr.ip Y W + r / 2 * pr.pnorm (Y - V) ^ 2 ≤
        pr.F X + pr.ip X W + r / 2 * pr.pnorm (X - V) ^ 2) → Y = Xp) ∧
    ∀ s (x : EuclideanSpace ℝ (Fin n)),
      (x ∈ pr.C s ∧ -(W s) - r • (x - V s) ∈ subdiff (pr.f s) x +
        FirstOrderOpt.ConvexTheory.normalCone (pr.C s) x) ↔
      (x ∈ pr.C s ∧ ∀ z ∈ pr.C s, pr.subObj s (V s) (W s) r x ≤ pr.subObj s (V s) (W s) r z) := by sorry

end ProgHedging.Convex
