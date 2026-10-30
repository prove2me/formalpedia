-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_approximateDesigns
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.approximateDesigns
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:05:29.617367+00:00
-- url     : https://prove2.me/theorems/9f2bc6b4-7966-454a-993a-e8ea9903f849
-- title:
--   Quantitative approximate designs in both architectures
-- statement:
--   Let $n$ be the number of qubits. The law $\nu_n$ chooses uniformly one of the $n$ ordered neighboring pairs on the periodic ring and applies an independent Haar $U(4)$ gate. For even $n$, $\nu_n^{\rm bw}$ first applies independent Haar gates on $(1,2),(3,4),\ldots$ and then on $(2,3),(4,5),\ldots,(n,1)$. Each brickwork step has two parallel gate layers. Write $\mu_H$ for normalized Haar measure and
--   $$g(\nu,t)=\left\|\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\nu(U)-\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\mu_H(U)\right\|_\infty.$$
--   The norm is the operator norm. Set $L(t)=\lceil2\log_2(4t)+\tfrac32\sqrt{\log_2(4t)}\rceil$ and $F(t)=(\ln t)^5t^{4+3/\sqrt{\log_2t}}$ when $t\ge2$.
--
--   Here an $\epsilon$-approximate unitary $t$-design means that its $t$-fold twirl differs from the Haar twirl by at most $\epsilon/2^{nt}$ in diamond norm, without a factor of $1/2$. Convolution powers denote independent steps. There exists one absolute $C>0$, chosen before $n,t,\epsilon,k$, such that for integers $n\ge2$, $t\ge2$, $n\ge L(t)$, $k\ge0$, and $0<\epsilon<1$,
--   $$k\ge CnF(t)\bigl(2nt+\log_2(1/\epsilon)\bigr)\ \Longrightarrow\ \nu_n^{*k}\text{ is an }\epsilon\text{-approximate unitary }t\text{-design}.$$
--   For even $n$, the same constant also gives
--   $$k\ge CF(t)\bigl(2nt+\log_2(1/\epsilon)\bigr)\ \Longrightarrow\ (\nu_n^{\rm bw})^{*k}\text{ is an }\epsilon\text{-approximate unitary }t\text{-design}.$$
--   This is the paper's precise quantitative design statement. It asserts the additive convention only and does not assign the corollary constant the theorem's numerical value.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 8, Corollary 1 (Unitary designs), Eqs.(21)–(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.8, Corollary 1, Eqs.(21)–(22): one absolute positive constant for both
architectures, quantified before system size, moment, error, and step count.
Only Definition 1(1) is claimed; the printed relative convention is deferred. -/
theorem approximateDesigns :
    ∃ C : ℝ, 0 < C ∧ ∀ (n t k : ℕ) (epsilon : ℝ),
      2 ≤ n → 2 ≤ t → reductionLength t ≤ n → 0 < epsilon → epsilon < 1 →
      ((C * n * designFactor t *
        (2 * (n : ℝ) * t + Real.logb 2 (1 / epsilon)) ≤ (k : ℝ) →
        IsApproximateDesign (steps (localHaarRingLaw n) k) t epsilon) ∧
      (Even n → C * designFactor t *
        (2 * (n : ℝ) * t + Real.logb 2 (1 / epsilon)) ≤ (k : ℝ) →
        IsApproximateDesign (steps (brickworkLaw n) k) t epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
