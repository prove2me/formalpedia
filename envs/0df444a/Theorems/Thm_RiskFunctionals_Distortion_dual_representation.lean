-- Prove2me | Theorems.Thm_RiskFunctionals_Distortion_dual_representation
-- name    : RiskFunctionals.Distortion.dual_representation
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:09.894915+00:00
-- url     : https://prove2.me/theorems/a634868c-67b6-486e-85ed-9a459c74339c
-- title:
--   Proposition 2.65 — $\mathcal A_H(Y)=\inf\{\mathbb E(YZ): Z=h(U),\ U\text{ uniform}\}$, attained at $Z=h(G(Y)-V_Y)$
-- statement:
--   Let $H$ be a differentiable distortion function on $[0,1]$ with derivative $h$, and $H(p)=\int_0^p h(\alpha)\,d\alpha$. Let $Y$ be a random variable on $(\Omega,\mathcal F,\mathbb P)$ with distribution function $G\in\mathcal G_H$, let $U$ be a uniform $[0,1]$ variable independent of $Y$, and $V_Y=(1-U)[G(Y)-G(Y-)]$ as in (2.68). Then
--
--   1. $$\mathcal A_H(Y)=\inf\{\mathbb E(YZ) : Z=h(U'),\ U'\text{ uniform in }[0,1]\}; \tag{2.70}$$
--   2. which is the same as
--   $$\mathcal A_H(Y)=\inf\{\mathbb E(YZ) : Z\prec_{CXD}Z^*\},\qquad Z^*=h(U'),\ U'\text{ uniformly }[0,1]\text{ distributed};$$
--   3. the infimum in (2.70) is attained for $Z=h(G(Y)-V_Y)$.
--
--   This is the dual (robust) representation of a distortion functional: the weight $Z$ ranges over the rearrangements of the distortion density, or over their convex-order minorants.
--
--   **Formalization Note** Stated as printed, with no concavity of $H$: by finding F1 it is false for $H(p)=p^2$ and $Y$ uniform on $[0,1]$, and the variant `RiskFunctionals.Distortion.dual_representation_corrected` adds "$H$ concave". Each infimum is stated as a greatest lower bound of the set of values $\mathbb E(YZ)$ over feasible $Z$ for which $YZ$ is integrable; in part 2, $Z$ is measurable and integrable and its law is dominated in the convex order by the law of $h$ under Lebesgue measure on $[0,1]$ (the law of $h(U')$ for any uniform $U'$). Part 3 says that $G(Y)-V_Y$ is uniform, $Y\,h(G(Y)-V_Y)$ is integrable, and its expectation equals $\mathcal A_H(Y)$. "Differentiable" is one-sided at the endpoints; $h$ is assumed measurable and integrable on $[0,1]$; $U$ is independent of $Y$, as Proposition 1.3 behind (2.68) requires. The book prints $V_Y=(1-U)[G(Y-)-G(Y)]$; with that sign $G(Y)-V_Y=G(Y)+(1-U)[G(Y)-G(Y-)]$, which contradicts the identity in (2.68) at every atom and can exceed $1$, so the sign is a typo and $V_Y=(1-U)[G(Y)-G(Y-)]$ is used, which makes $G(Y)-V_Y$ the generalized quantile transform $(1-U)G(Y-)+UG(Y)$ of Proposition 1.3.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 86–87, Proposition 2.65

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
import Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
import Definitions.Def_RiskFunctionals_Distortion_Orders

namespace RiskFunctionals.Distortion

open MeasureTheory ProbabilityTheory

/-- Proposition 2.65 (Pflug & Römisch, pp. 86–87), as printed: let `H` be a differentiable
distortion function, with derivative `h` on `[0, 1]` and `H(p) = ∫₀^p h(α) dα`. For `Y` with
distribution `G ∈ 𝒢_H`:
`𝒜_H(Y) = inf {𝔼(Y Z) : Z = h(U), U uniform in [0, 1]}` (2.70), which is the same as
`𝒜_H(Y) = inf {𝔼(Y Z) : Z ≺_CXD Z*}`, `Z* = h(U)` with `U` uniformly `[0, 1]` distributed; and the
infimum in (2.70) is attained for `Z = h(G(Y) − V_Y)`, `V_Y = (1 − U)[G(Y) − G(Y−)]` as in (2.68) (the book
prints `[G(Y−) − G(Y)]`, a sign typo: only the corrected sign gives the identity of (2.68))
(`U` uniform and independent of `Y`). Infima are stated as greatest lower bounds (`IsGLB`) of the
sets of values `𝔼(Y Z)` over feasible `Z` with `Y Z` integrable. No concavity of `H` is assumed,
as on the page (finding F1: the statement is false for `H(p) = p²`). -/
theorem dual_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (H : StieltjesFunction ℝ) (h : ℝ → ℝ) (hhm : Measurable h)
    (hhi : IntegrableOn h (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ p ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt H (h p) (Set.Icc (0 : ℝ) 1) p)
    (hH : ∀ p ∈ Set.Icc (0 : ℝ) 1, H p = ∫ q in (0 : ℝ)..p, h q)
    (Y U : Ω → ℝ) (hY : Measurable Y) (hU : IsUniform01 P U) (hind : IndepFun Y U P)
    (hG : InDistortionDomain H (P.map Y)) :
    -- (2.70): 𝒜_H(Y) = inf {𝔼(Y Z) : Z = h(U'), U' uniform in [0, 1]}
    IsGLB {x : ℝ | ∃ U' : Ω → ℝ, IsUniform01 P U' ∧
        Integrable (fun ω => Y ω * h (U' ω)) P ∧ x = ∫ ω, Y ω * h (U' ω) ∂P}
      (distortionFunctional H (P.map Y)) ∧
    -- 𝒜_H(Y) = inf {𝔼(Y Z) : Z ≺_CXD Z*}, Z* = h(U') with U' uniform in [0, 1]
    IsGLB {x : ℝ | ∃ Z : Ω → ℝ, Measurable Z ∧ Integrable Z P ∧
        CXD (P.map Z) ((volume.restrict (Set.Icc (0 : ℝ) 1)).map h) ∧
        Integrable (fun ω => Y ω * Z ω) P ∧ x = ∫ ω, Y ω * Z ω ∂P}
      (distortionFunctional H (P.map Y)) ∧
    -- the infimum in (2.70) is attained for Z = h(G(Y) − V_Y), V_Y = (1 − U)[G(Y) − G(Y−)]
    (IsUniform01 P (fun ω => distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) ∧
      Integrable (fun ω => Y ω * h (distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω)))) P ∧
      ∫ ω, Y ω * h (distributionFunction (P.map Y) (Y ω) -
        (1 - U ω) * (distributionFunction (P.map Y) (Y ω) -
          distributionFunctionLeft (P.map Y) (Y ω))) ∂P = distortionFunctional H (P.map Y)) := by sorry

end RiskFunctionals.Distortion
