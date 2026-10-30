-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_conditional_iid_constructive
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.conditional_iid_constructive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:51:52.730437+00:00
-- url     : https://prove2.me/theorems/c5942b2a-3424-4172-9553-ad8d9e4e7b3b
-- title:
--   Conditional IID exponent bound, constructive form
-- statement:
--   Let $A$ be finite and nonempty, let $\mu$ be a probability measure on a measurable space $E$, and let $p_e(a)$ be a measurable conditional probability vector. Define $\phi(t)=\log\int(\sum_a p_e(a)^{1/(1-t)})^{1-t}\,d\mu(e)$ and $g_E(s)=-\log\int\sum_a p_e(a)^{1+s}\,d\mu(e)$, with $g_E(0)=0$. Leakage is full $L^1$ distance from a uniform key independent of Eve. Take iid copies of the joint source, positive $M_n$ with $\log M_n/n\to R$, and any independent universal2 ensembles on $A^n$. For every $0\le t\le1/2$,
--   $$\mathbb E_Xd_{1,n}\le3M_n^te^{n\phi(t)},\qquad\liminf_n-\frac1n\log\mathbb E_Xd_{1,n}\ge\max_{0\le t\le1/2}\{-\phi(t)-tR\}.$$
--   For each $n$, one deterministic extractor attains the minimum of the finite upper bound over $t\in[0,1/2]$. The iid side-information measure and conditional vectors are genuine products. This constructive statement avoids the malformed operational definition of $e_1$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 11, Conditional IID exponent bound, constructive form

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.10–11, tensorization and deterministic selection from (68).
This conclusion uses no malformed operational rate constraint from e_1. -/
theorem conditional_iid_constructive {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu]
    (p : E → A → ℝ) (hp : IsConditionalLaw p)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (h : (n : ℕ) → HashEnsemble (Fin n → A) (M n)) (hu : ∀ n, Universal2 (h n))
    (R : ℝ) (hrate : Tendsto (fun n => Real.log (M n : ℝ) / (n : ℝ)) atTop (𝓝 R)) :
    (∀ n (t : ℝ), t ∈ Set.Icc (0 : ℝ) (1 / 2) →
      expectedConditionalLeakage (Measure.pi (fun _ : Fin n => mu)) (conditionalIid p n) (h n) ≤
        3 * (M n : ℝ) ^ t * Real.exp ((n : ℝ) * conditionalPhi mu p t)) ∧
    (conditionalPhiExponent mu p R : EReal) ≤ Filter.liminf (fun n => negativeLogRate
      (expectedConditionalLeakage (Measure.pi (fun _ : Fin n => mu))
        (conditionalIid p n) (h n)) n) atTop ∧
    (∀ n, ∃ f : (Fin n → A) → Fin (M n),
      conditionalLeakage (Measure.pi (fun _ : Fin n => mu)) (conditionalIid p n) f ≤
        sInf ((fun t : ℝ => 3 * (M n : ℝ) ^ t *
          Real.exp ((n : ℝ) * conditionalPhi mu p t)) '' Set.Icc 0 (1 / 2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
