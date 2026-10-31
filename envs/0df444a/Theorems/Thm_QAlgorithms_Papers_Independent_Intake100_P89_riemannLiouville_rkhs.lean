-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_riemannLiouville_rkhs
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.riemannLiouville_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:53:51.989139+00:00
-- url     : https://prove2.me/theorems/ea0501c2-9c72-43af-b450-4f2a4e3bf5cb
-- title:
--   Lemma 10.2: Riemann–Liouville RKHS
-- statement:
--   Let $\alpha>0$ and let $R^\alpha$ be the continuous Riemann–Liouville process $R_t^\alpha=\int_0^t(t-s)^{\alpha-1/2}\,dW_s$. With the Gamma-normalized fractional integral, its covariance RKHS is
--   $$H_{R^\alpha}=I^{\alpha+1/2}(L^2[0,1]),\qquad\|I^{\alpha+1/2}f\|_H=\frac{\|f\|_2}{\Gamma(\alpha+1/2)}.$$
--   The corresponding inner product is $\langle f,g\rangle_2/\Gamma(\alpha+1/2)^2$. Fractional synthesis is injective, and the same function RKHS is obtained in $C[0,1]$.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 21, Lemma 10.2: Riemann–Liouville RKHS

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Lemma 10.2: Riemann–Liouville RKHS, arXiv:0805.3252v1, PDF p.21.
PDF p.21 rendered: lemma uses unsquared norms and one Gamma; equation (10.2) uses Gamma squared. The constructed process is the actual Wiener-kernel process; existence of its continuous version and its covariance are conclusions. -/
theorem riemannLiouville_rkhs
(W : Omega → C(Time, ℝ)) (hW : StandardBrownian P W) (a : ℝ) (ha : 0 < a) :
    RiemannLiouville P a (rlPath P W a) ∧
    (∀ t : Time, MemLp (fun o => rlPath P W a o t) 2 P ∧
      toL2 P (fun o => rlPath P W a o t) = wienerIntegral P W (rlKernel a t)) ∧
    processRKHS P (fun t o => rlPath P W a o t) =
      Set.range (fun f : TimeL2 => fractionalIntegral (a + 1 / 2) f) ∧
    (fun h : C(Time, ℝ) => fun t => h t) '' banachRKHS P (rlPath P W a) =
      Set.range (fun f : TimeL2 => fractionalIntegral (a + 1 / 2) f) ∧
    Function.Injective (fun f : TimeL2 => fractionalIntegral (a + 1 / 2) f) ∧
    (∀ f : TimeL2,
      processNorm P (fun t o => rlPath P W a o t) (fractionalIntegral (a + 1 / 2) f) =
        ‖f‖ / Real.Gamma (a + 1 / 2)) ∧
    ∀ f g : TimeL2,
      processInner P (fun t o => rlPath P W a o t)
        (fractionalIntegral (a + 1 / 2) f) (fractionalIntegral (a + 1 / 2) g) =
          inner ℝ f g / (Real.Gamma (a + 1 / 2)) ^ 2 := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
