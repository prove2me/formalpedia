-- Prove2me | Theorems.Thm_SelfScaledLongStep_AffinePot_theorem_7_4_b
-- name    : SelfScaledLongStep.AffinePot.theorem_7_4_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:10.40486+00:00
-- url     : https://prove2.me/theorems/7f072a6e-5cea-44be-8674-df00626926db
-- title:
--   Theorem 7.4 (b), pp. 31–32 — if µ ≥ 2ν, one affine potential-reduction step lowers Φ by (‖p‖²_x̂/|p|²_x̂)(1 − ln 2) ≥ 1 − ln 2
-- statement:
--   Let $K \subseteq E$ be a self-scaled cone with $\nu$-self-scaled barrier $F$, and consider the conic problem
--   $$\min\ \langle c, x\rangle\quad\text{s.t.}\quad Ax = b,\ x \in K,$$
--   with $A$ surjective, a strictly feasible dual point, and an objective that is not constant on the feasible region. Let $\zeta^*$ be the optimal value and, for $\mu > 0$, let $\Phi(x;\zeta) = \mu\ln(\langle c, x\rangle - \zeta) + F(x)$ be the primal potential (7.1).
--
--   Let $\hat x \in S^0(P)$ (so $\hat x \in \operatorname{int}K$, $A\hat x = b$) and $\hat\zeta \le \zeta^*$. Let $p(c)$, $p(d)$ be the projections of $c$ and $d = F'(\hat x)$ into $\ker A$ with respect to $F''(\hat x)$ (7.12), let $\zeta^+$ be the updated lower bound (7.17), $\lambda^+ = (\langle c, \hat x\rangle - \zeta^+)/\mu$, $p = p(c) + \lambda^+ p(d)$, and $p_+ = \sigma_{\hat x}(p)$.
--
--   If $\mu \ge 2\nu$, there is $\alpha > 0$ such that $x^+ = \hat x - \alpha p$ lies in $S^0(P)$, $\langle c, x^+\rangle > \zeta^+$, and
--   $$\Phi(x^+;\zeta^+) \le \Phi(\hat x;\hat\zeta) - \frac{\|p\|^2_{\hat x}}{(\max\{p_+, |p|_{\hat x}\})^2}(1 - \ln 2) = \Phi(\hat x;\hat\zeta) - \frac{\|p\|^2_{\hat x}}{|p|^2_{\hat x}}(1 - \ln 2) \le \Phi(\hat x;\hat\zeta) - (1 - \ln 2).\qquad (7.19)$$
--
--   This is the long-step half of Theorem 7.4: the step may go a large fraction of the way to the boundary of $K$, and the guaranteed decrease $(\|p\|^2_{\hat x}/|p|^2_{\hat x})(1-\ln 2)$ is typically much larger than the constant $1 - \ln 2$. Iterating it gives an $O(\mu\ln(1/\epsilon))$-iteration method.
--
--   **Formalization Note** $E = E^* = \mathbb R^n$ through the inner product. $\|p\|_{\hat x} = \langle F''(\hat x)p, p\rangle^{1/2}$ is `lnorm F x̂ p`, $|p|_{\hat x} = \max\{\sigma_{\hat x}(p), \sigma_{\hat x}(-p)\}$ is `absn K x̂ p`, $\sigma_{\hat x}(p) = \min\{\beta \ge 0: \beta\hat x - p \in K\}$ is `sigma K x̂ p`. $\zeta^+$ is `zetaPlus` (best-lower-bound form of (7.17)) and $p$ is `affDir`; the projections are given as data satisfying (7.12). The paper's "a suitable value of $\alpha$" is an existential over $\alpha > 0$. The conjunct $\langle c, x^+\rangle - \zeta^+ > 0$ is stated so that $\Phi(x^+;\zeta^+)$ is the genuine logarithm; the paper presupposes it. Standing assumptions carried as hypotheses: (6.1), (6.3), the §7 non-constant objective, $\nu \ge 1$. Inherited conventions: nondegeneracy of $F''$, and the conjugate barrier as an `sSup` over $\operatorname{int}K$.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 31–32, Theorem 7.4 (b), (7.19)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_AffinePot_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.AffinePot

/-- **Theorem 7.4 (b)** (pp. 31–32). Let `ζ⁺` be the updated lower bound (7.17) and
`p = p(c) + λ(ζ⁺) p(d)` the search direction, `p₊ = σ_x̂(p)`. If `µ ≥ 2ν`, a suitable
`α > 0` gives `x⁺ = x̂ − αp ∈ S⁰(P)` with (7.19):
`Φ(x⁺; ζ⁺) ≤ Φ(x̂; ζ̂) − (‖p‖²_x̂/(max{p₊, |p|_x̂})²)(1 − ln 2)
           = Φ(x̂; ζ̂) − (‖p‖²_x̂/|p|²_x̂)(1 − ln 2) ≤ Φ(x̂; ζ̂) − (1 − ln 2)`. -/
theorem theorem_7_4_b {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hD : ∃ y s, IsDualStrict K A c y s)
    (hnc : ∃ x₁ x₂, (x₁ ∈ K ∧ A x₁ = b) ∧ (x₂ ∈ K ∧ A x₂ = b) ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (μ : ℝ) (hμ : 2 * ν ≤ μ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : IsPrimalStrict K A b xh) (ζh : ℝ) (hζh : ζh ≤ zetaStar K A b c)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F A xh c yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F A xh (gradient F xh) yd pd) :
    let ζp := zetaPlus K F c xh pc pd ζh
    let p := affDir K F μ c xh pc pd ζh
    (∃ α : ℝ, 0 < α ∧ IsPrimalStrict K A b (xh - α • p) ∧ 0 < ⟪c, xh - α • p⟫_ℝ - ζp ∧
      affPotential F μ c ζp (xh - α • p) ≤ affPotential F μ c ζh xh -
        (lnorm F xh p) ^ 2 / (max (sigma K xh p) (absn K xh p)) ^ 2 * (1 - Real.log 2)) ∧
    (lnorm F xh p) ^ 2 / (max (sigma K xh p) (absn K xh p)) ^ 2 * (1 - Real.log 2) =
      (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ∧
    affPotential F μ c ζh xh - (lnorm F xh p) ^ 2 / (absn K xh p) ^ 2 * (1 - Real.log 2) ≤
      affPotential F μ c ζh xh - (1 - Real.log 2) := by sorry

end SelfScaledLongStep.AffinePot
