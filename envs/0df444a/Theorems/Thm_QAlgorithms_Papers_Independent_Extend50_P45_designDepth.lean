-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_designDepth
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.designDepth
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:02:45.723017+00:00
-- url     : https://prove2.me/theorems/b235d89e-4b64-444f-98f5-2362610b5d30
-- title:
--   Fixed-error brickwork design depth
-- statement:
--   Let $n$ be the number of qubits. The law $\nu_n$ chooses uniformly one of the $n$ ordered neighboring pairs on the periodic ring and applies an independent Haar $U(4)$ gate. For even $n$, $\nu_n^{\rm bw}$ first applies independent Haar gates on $(1,2),(3,4),\ldots$ and then on $(2,3),(4,5),\ldots,(n,1)$. Each brickwork step has two parallel gate layers. Write $\mu_H$ for normalized Haar measure and
--   $$g(\nu,t)=\left\|\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\nu(U)-\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\mu_H(U)\right\|_\infty.$$
--   The norm is the operator norm. Set $L(t)=\lceil2\log_2(4t)+\tfrac32\sqrt{\log_2(4t)}\rceil$ and $F(t)=(\ln t)^5t^{4+3/\sqrt{\log_2t}}$ when $t\ge2$.
--
--   Here an $\epsilon$-approximate unitary $t$-design means that its $t$-fold twirl differs from the Haar twirl by at most $\epsilon/2^{nt}$ in diamond norm, without a factor of $1/2$. Convolution powers denote independent steps. For each fixed $0<\epsilon<1$, there exist $K>0$, an integer $t_0\ge2$, and $h:\mathbb N\to\mathbb R$ tending to zero, all independent of $n,t$, such that every even $n\ge2$ and $t\ge t_0$ with $n\ge L(t)$ admit an integer $k\ge0$ satisfying
--   $$2k\le\left\lceil Knt^{5+h(t)}\right\rceil,\qquad (\nu_n^{\rm bw})^{*k}\text{ is an }\epsilon\text{-approximate unitary }t\text{-design}.$$
--   This is the title-level consequence of the quantitative brickwork bound, counting parallel gate layers.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 1, Unnumbered main result: approximate designs in depth O(n t^(5+o(1)))

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.1, title/abstract, pinned by p.8 Eq.(22): fixed-error brickwork designs
in O(n t^(5+o(1))) parallel gate layers. Each step has two layers.
All witnesses are uniform over admissible n and t. -/
theorem designDepth (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1) :
    ∃ (K : ℝ) (t0 : ℕ) (h : ℕ → ℝ), 0 < K ∧ 2 ≤ t0 ∧
      Filter.Tendsto h Filter.atTop (nhds 0) ∧
      ∀ n t : ℕ, 2 ≤ n → Even n → t0 ≤ t → reductionLength t ≤ n →
        ∃ k : ℕ, 2 * k ≤ ⌈K * n * (t : ℝ) ^ (5 + h t)⌉₊ ∧
          IsApproximateDesign (steps (brickworkLaw n) k) t epsilon := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
