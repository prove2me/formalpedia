-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_fractional_process_identity
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.fractional_process_identity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:53:29.519502+00:00
-- url     : https://prove2.me/theorems/7f7e9138-e944-4b06-9b01-b6e237610f7c
-- title:
--   §10, unnumbered fractional-integral representation
-- statement:
--   Use the Gamma-normalized fractional integral $I^af(t)=\Gamma(a)^{-1}\int_0^t(t-s)^{a-1}f(s)\,ds$. At every positive integer order it agrees with ordinary repeated integration whenever the displayed integrals exist. Let $W$ be standard continuous Brownian motion and let $R^\alpha$ be the continuous version of $\int_0^t(t-s)^{\alpha-1/2}\,dW_s$. For $\alpha>1/2$,
--   $$R_t^\alpha=\Gamma(\alpha+1/2)\,I^{\alpha-1/2}W(t)\quad\text{for every }t\in[0,1],\quad P\text{-a.s.}$$
--   The process is constructed from the canonical deterministic Wiener integral and a continuous version, rather than from a freely chosen Gaussian process. Order zero is excluded from the positive-order formula.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 21, §10, unnumbered fractional-integral representation

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

/-- §10, unnumbered fractional-integral representation, arXiv:0805.3252v1, PDF p.21.
The canonical Wiener map is inverse Brownian covariance synthesis on primitives. The common domain clauses express the source if-it-exists convention for ordinary integrals. The almost-sure equality is simultaneous in t for the chosen continuous version. -/
theorem fractional_process_identity
(W : Omega → C(Time, ℝ)) (hW : StandardBrownian P W) :
    (∀ (k : ℕ) (hk : 0 < k) (f : Time → ℝ),
      FractionalDomain (k : ℝ) f → IteratedIntegralDomain k f →
      fractionalIntegral (k : ℝ) f = iterPrimitive k f) ∧
    ∀ a : ℝ, 1 / 2 < a →
      (∀ t : Time, MemLp (fun o => rlPath P W a o t) 2 P ∧
        toL2 P (fun o => rlPath P W a o t) = wienerIntegral P W (rlKernel a t)) ∧
      (∀ᵐ o ∂P, ∀ t : Time,
        rlPath P W a o t = Real.Gamma (a + 1 / 2) *
          fractionalIntegral (a - 1 / 2) (W o) t) := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
