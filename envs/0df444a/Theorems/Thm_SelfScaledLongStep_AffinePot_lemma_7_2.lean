-- Prove2me | Theorems.Thm_SelfScaledLongStep_AffinePot_lemma_7_2
-- name    : SelfScaledLongStep.AffinePot.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:52.413106+00:00
-- url     : https://prove2.me/theorems/d1061e77-5bdb-4875-bece-e5ba694e5616
-- title:
--   Lemma 7.2, p. 31 — λ⁺ ≤ ‖p‖_x̂ if µ ≥ ν + √ν, and λ⁺ ≤ |p|_x̂ if µ ≥ 2ν
-- statement:
--   Let $K$ be a self-scaled cone with $\nu$-self-scaled barrier $F$, and consider $(P)$: $\min\langle c, x\rangle$ s.t. $Ax = b$, $x \in K$, where $A$ is surjective, the dual $(D)$ has a strictly feasible point, and the objective is not constant on the feasible region of $(P)$. Let $\mu > \nu$, let $\hat x \in S^0(P)$ and let $\hat\zeta \le \zeta^*$ be a lower bound on the optimal value. With the projections $p(c)$, $p(d)$ of (7.12), the updated lower bound $\zeta^+$ of (7.17), $\lambda^+ = (\langle c, \hat x\rangle - \zeta^+)/\mu$ and the search direction $p = p(c) + \lambda^+ p(d)$:
--
--   1. if $\mu \ge \nu + \sqrt\nu$, then $\lambda^+ \le \|p\|_{\hat x}$;
--   2. if $\mu \ge 2\nu$, then $\lambda^+ \le |p|_{\hat x}$,
--
--   where $\|p\|_{\hat x} = \langle F''(\hat x)p, p\rangle^{1/2}$ and $|p|_{\hat x} = \max\{\sigma_{\hat x}(p), \sigma_{\hat x}(-p)\}$, $\sigma_{\hat x}(p) = \min\{\beta \ge 0 : \beta\hat x - p \in K\}$.
--
--   The lemma bounds the scaling factor $\lambda^+$ of the search direction by its own length, which is what turns the bound (7.20) on the potential change into a constant decrease in Theorem 7.4.
--
--   **Formalization Note** $E = E^* = \mathbb R^n$. $\|p\|_{\hat x}$ is `lnorm F x̂ p`, $|p|_{\hat x}$ is `absn K x̂ p`, $\sigma_{\hat x}$ is `sigma K x̂`. $\zeta^+$ is `zetaPlus` (the best-lower-bound form of (7.17), see the definitions item) and $p$ is `affDir`. Standing assumptions carried as hypotheses: (6.1) surjectivity of $A$, (6.3) strict dual feasibility, the §7 assumption that the objective is not constant on the feasible region (stated as two feasible points with different objective values), $\mu > \nu$ (§7.2), $\nu \ge 1$. The inherited conventions are nondegeneracy of $F''$ and the conjugate barrier as an `sSup` over $\operatorname{int} K$.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 31, Lemma 7.2

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_AffinePot_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.AffinePot

/-- **Lemma 7.2** (p. 31). With `ζ⁺` the updated lower bound (7.17), `λ⁺ = λ(ζ⁺)` and
`p = p(c) + λ⁺ p(d)`: if `µ ≥ ν + √ν` then `λ⁺ ≤ ‖p‖_x̂`, while if `µ ≥ 2ν` then
`λ⁺ ≤ |p|_x̂ = max{σ_x̂(p), σ_x̂(−p)}`. -/
theorem lemma_7_2 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ y s, IsDualStrict K A c y s)
    (hnc : ∃ x₁ x₂, (x₁ ∈ K ∧ A x₁ = b) ∧ (x₂ ∈ K ∧ A x₂ = b) ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (μ : ℝ) (hμ : ν < μ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsPrimalStrict K A b xh) (ζh : ℝ) (hζh : ζh ≤ zetaStar K A b c)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F A xh c yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F A xh (gradient F xh) yd pd) :
    let ζp := zetaPlus K F c xh pc pd ζh
    let p := affDir K F μ c xh pc pd ζh
    (ν + Real.sqrt ν ≤ μ → lam μ c xh ζp ≤ lnorm F xh p) ∧
    (2 * ν ≤ μ → lam μ c xh ζp ≤ absn K xh p) := by sorry

end SelfScaledLongStep.AffinePot
