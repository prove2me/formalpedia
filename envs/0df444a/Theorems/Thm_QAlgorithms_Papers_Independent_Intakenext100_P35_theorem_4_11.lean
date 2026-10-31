-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_4_11
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_4_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:24:33.099575+00:00
-- url     : https://prove2.me/theorems/3bb4b5f5-764a-445f-aeb4-5f46c25c1f29
-- title:
--   Theorem 4.11
-- statement:
--   Every $f\in\mathcal H_{\pi/2}$ has a representation
--
--   $$f=f(\infty)+\mathcal Lg,\qquad g\in L^1(\mathbb R_+).$$
--
--   Consequently $\mathcal H_{\pi/2}\subset\mathcal{LM}\subset\mathcal B$ continuously. Also $\mathcal H_{\pi/2}\subset\mathcal D_s$ continuously for every $s>-1$, while restriction maps $\mathcal D_s\to\mathcal H_\psi$ are continuous for every $0<\psi<\pi/2$. These embeddings connect the three calculi.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 22, Theorem 4.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 4.11, arXiv:2202.03143v1, PDF page(s) 22. -/
theorem theorem_4_11
:
    (∃ C : ℝ, 0 < C ∧ ∀ f, HardySobolevClass (Real.pi / 2) f →
      (∃ g : ℝ → ℂ, Integrable g positiveVolume ∧
        EqOn f (fun z => infinityValue f +
          ∫ t, Complex.exp (-z * (t : ℂ)) * g t ∂positiveVolume) hp) ∧
      LM f ∧ hpSize f ≤ ENNReal.ofReal C * hSize (Real.pi / 2) f) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f, LM f → BesovClass f ∧ bSize f ≤ ENNReal.ofReal C * hpSize f) ∧
    (∀ s : ℝ, -1 < s → ∃ C : ℝ, 0 < C ∧ ∀ f, HardySobolevClass (Real.pi / 2) f →
      D s f ∧ dSize s f ≤ ENNReal.ofReal C * hSize (Real.pi / 2) f) ∧
    (∀ s psi : ℝ, -1 < s → 0 < psi → psi < Real.pi / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ f, D s f → HardySobolevClass psi f ∧
        hSize psi f ≤ ENNReal.ofReal C * dSize s f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
