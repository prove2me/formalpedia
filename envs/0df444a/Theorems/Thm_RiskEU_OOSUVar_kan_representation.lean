-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_kan_representation
-- name    : RiskEU.OOSUVar.kan_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:51.685516+00:00
-- url     : https://prove2.me/theorems/3589a9d3-8d15-4689-930d-7e4d3e09ae35
-- title:
--   Kan et al. (2022b, Proposition 1) as restated, (IA45)–(IA48), pp. IA35–IA36 — joint stochastic representation of the out-of-sample mean and variance of ŵ*(κ)
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Let $z_2,u_0,v_2,w_1,w_2,s_1,s_2,x_{11},x_{21},a,b,c$ be mutually independent random variables on some probability space with the laws
--
--   $$z_2\sim\mathcal N(\sqrt T\psi,1),\ u_0\sim\chi^2_{N-2},\ v_2\sim\chi^2_{T-N+1},\ w_1\sim\chi^2_{T-N+3},\ w_2\sim\chi^2_{T-N+2},\ s_1\sim\chi^2_{N-4},\ s_2\sim\chi^2_{N-3},$$
--
--   and $x_{11},x_{21},a,b,c\sim\mathcal N(0,1)$, where $\psi=\sqrt{\psi^2}$ is computed from the market. Define $y_1,y_2$ by (IA45)–(IA46) with footnote 6's convention for $N\le3$. Then the pair $\big(\hat w^\star(\kappa)^\top\mu,\ \hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)\big)$ has the same joint law as the pair of right-hand sides
--
--   $$\Big(\mu_g+\frac{\sigma_g\psi\sqrt{v_2}}{\sqrt{z_2^2+u_0}}\Big(\frac{\sqrt{u_0}y_1}{\sqrt{v_2}}+\frac{az_2}{v_2}\Big)+\frac{\kappa\sqrt T\psi}{\gamma v_2}\Big(\frac{x_{21}\sqrt{u_0}}{\sqrt{w_2}}+z_2\Big),$$
--   $$\ \sigma_g^2\Big(1+y_1^2+y_2^2+\frac{s_1}{w_1}+\frac{a^2}{v_2}\Big)+\frac{\kappa^2T(z_2^2+u_0)}{\gamma^2v_2^2}\Big(1+\frac{x_{21}^2+s_2}{w_2}\Big)+\frac{2\kappa\sqrt T\sigma_g\sqrt{z_2^2+u_0}}{\gamma v_2}\Big(\frac{a}{\sqrt{v_2}}+\frac{x_{21}y_1}{\sqrt{w_2}}+\frac{\sqrt{s_2}y_2}{\sqrt{w_2}}\Big)\Big)$$
--
--   ((IA47)–(IA48)).
--
--   This representation, due to Kan, Wang and Zhou (2022b), reduces every moment of the out-of-sample mean and variance of $\hat w^\star(\kappa)$ to moments of independent normal and chi-squared variables. The two coordinates must be represented *jointly*, since the covariance (IA68) is computed on the same variables.
--
--   **Formalization Note.** The statement is an equality of push-forward measures on $\mathbb R^2$: the law of the pair under the sampling measure equals the law of the representing pair under the auxiliary measure, for any probability space carrying a Kan family. Footnote 6 is built into the definitions (see `KanRepresentation`).
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, Kan et al. (2022b, Proposition 1) as restated, (IA45)–(IA48) and footnote 6, pp. IA35–IA36

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem kan_representation {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T M.psi2 Q X) :
    P.map (fun ω => (M.oosMean κ (sampleData r ω), M.oosVar κ (sampleData r ω))) =
      Q.map (fun ω' => (M.kanMeanRep T κ (fun i => X i ω'), M.kanVarRep T κ (fun i => X i ω'))) := by sorry

end RiskEU.OOSUVar
