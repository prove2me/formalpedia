-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P02_thermalEntropy_amplifierInequality
-- name    : QAlgorithms.Papers.Independent.Frontier18.P02.thermalEntropy_amplifierInequality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:50:05.94367+00:00
-- url     : https://prove2.me/theorems/e26c1e80-94d1-49b4-8a62-4f565fc18758
-- title:
--   Theorem 8: amplifier extension of thermal-entropy inequality
-- statement:
--   Let $n\ge1$ be a finite integer, let $(p_x)_{x=1}^n$ be a nonnegative probability law, and let $y_0,y_1,\ldots,y_n\ge0$. For the thermal entropy $g(x)=(x+1)\log_2(x+1)-x\log_2x$, using $0\log_2 0=0$, suppose that $q>1$ is finite and
--   $$
--   \sum_{x=1}^n p_x g(y_x)=g(y_0).
--   $$
--   Then
--   $$
--   \sum_{x=1}^n p_xg(qy_x+q-1)\ge g(qy_0+q-1).
--   $$
--
--   This entropy inequality supplies the amplifier-gain extension needed to compare the common entropy-sharing parameters in the capacity converse. Zero probability weights and zero photon occupations are permitted.
-- source:
--   Capacities of Quantum Amplifier Channels, arXiv:1605.04922v3, PDF p. 10, Theorem 8: amplifier extension of thermal-entropy inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier18.P02

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.10, Theorem 8, (A4)--(A5). Fin n relabels the source's
indices 1,...,n. The nonnegative normalized law may have zero weights;
y0 and every yx lie in the physical thermal domain. The amplifier shift
is exactly q-1 and q>1; no entropy bound proved in the source is assumed. -/
theorem thermalEntropy_amplifierInequality (n : ℕ) (hn : 0 < n)
    (q y0 : ℝ) (hq : 1 < q) (hy0 : 0 ≤ y0)
    (p y : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hp_sum : ∑ x, p x = 1) (hy : ∀ x, 0 ≤ y x)
    (hentropy : ∑ x, p x * thermalEntropy (y x) = thermalEntropy y0) :
    thermalEntropy (q * y0 + q - 1) ≤
      ∑ x, p x * thermalEntropy (q * y x + q - 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P02

end
