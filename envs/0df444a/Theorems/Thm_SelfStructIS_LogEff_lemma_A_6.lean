-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_lemma_A_6
-- name    : SelfStructIS.LogEff.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:17.291368+00:00
-- url     : https://prove2.me/theorems/54c8cd97-50f9-400d-ba03-736ba568dc0a
-- title:
--   Lemma A.6, p. 33 (corrected) — M₂,ᵤ = E[exp(−t(u)(aᵤ + bᵤ)(Yᵤ)) 𝕀(Yᵤ ∈ lev⁺₁(Lᵤ))]
-- statement:
--   Let $X$ (in $\mathbb R^d$) have law $\mu$ with density $f_X$ and marginal densities $f_{X_i}$, satisfy Assumption 3.1, and let $Y=\Lambda(X)$ have density $f_Y$. Let $L$ be measurable, $\rho>0$, $0<l<u$ with $t(u)>0$, and let $T$ use the exponent $\kappa^{(1)}$. Assume the support condition of Proposition 2.1. Then, with $Y_u=Y/t(u)$, the second moment of the estimator is the Laplace-type functional
--   $$M_{2,u}=E\Big[\exp\big(-t(u)\,[a_u(Y_u)+b_u(Y_u)]\big)\,\mathbb I\big(Y_u\in\mathbb R^d_{++},\ L_u(Y_u)\ge1\big)\Big],$$
--   with $a_u,b_u$ as defined in this mission (Lemma A.6's display).
--
--   This representation reduces the efficiency question to a Varadhan-type asymptotic for $Y_u$.
--
--   **Formalization Note** As printed, the lemma has $F_u=a_u+b_u-2d\log t(u)/t(u)+\chi_{\mathrm{lev}^+_1(L_u)}$, i.e. a factor $t(u)^{2d}$ in front of the expectation. Redoing the paper's own computation (49) with $f_{Y_u}(p)=t(u)^d f_Y(t(u)p)$ (the proof writes it inverted) gives no such factor, so the corrected identity is stated; the slip does not affect Theorem 5.1 since $\log t(u)=o(t(u))$. The characteristic function $\chi$ ($0$ on the level set, $+\infty$ off it) is written as an indicator, since $e^{-\infty}=0$. The support condition (also needed by Proposition 2.1), the density of $Y$, the marginal densities and Assumption 3.1 are what the change of variables uses. $\lambda_i=f_{X_i}/\bar F_i$ is the hazard rate (p. 33 prints $f_{X_i}/\Lambda_i$).
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 33, Lemma A.6, (49)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler
import Definitions.Def_SelfStructIS_LogEff_Tail

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem lemma_A_6 (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (fX : (Fin d → ℝ) → ℝ) (hfX_meas : Measurable fX) (hfX_nonneg : ∀ x, 0 ≤ fX x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (fX x)))
    (fXi : Fin d → ℝ → ℝ)
    (hfXi : ∀ i, Measurable (fXi i) ∧ (∀ x, 0 ≤ fXi i x) ∧
      μ.map (fun x => x i) = volume.withDensity (fun x => ENNReal.ofReal (fXi i x)))
    (fY : (Fin d → ℝ) → ℝ) (hfY_meas : Measurable fY) (hfY_nonneg : ∀ y, 0 ≤ fY y)
    (hfY : μ.map (hazardVec μ) = volume.withDensity (fun y => ENNReal.ofReal (fY y)))
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (L : (Fin d → ℝ) → ℝ) (hL : Measurable L) (ρ : ℝ) (hρ : 0 < ρ)
    (u l : ℝ) (hl : 0 < l) (hlu : l < u) (ht : 0 < tfun μ ρ u)
    (hsupp : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
      0 < fX (Tmap .one ρ u l x) → u ≤ L (Tmap .one ρ u l x) → 0 < fX x) :
    M2 μ fX L ρ .one u l =
      ∫⁻ x, (if (∀ i, 0 < ((tfun μ ρ u)⁻¹ • hazardVec μ x) i) ∧
            1 ≤ Lu μ L ρ u ((tfun μ ρ u)⁻¹ • hazardVec μ x) then
          ENNReal.ofReal (Real.exp (-(tfun μ ρ u) *
            (aU μ fY .one ρ u l ((tfun μ ρ u)⁻¹ • hazardVec μ x) +
              bU μ fXi .one ρ u l ((tfun μ ρ u)⁻¹ • hazardVec μ x))))
        else 0) ∂μ := by sorry

end SelfStructIS.LogEff
