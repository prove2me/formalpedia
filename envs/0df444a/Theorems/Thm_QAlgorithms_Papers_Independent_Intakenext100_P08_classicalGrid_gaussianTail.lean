-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P08_classicalGrid_gaussianTail
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P08.classicalGrid_gaussianTail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:02:03.48644+00:00
-- url     : https://prove2.me/theorems/29d59c62-df09-4215-b6f1-a7e8ea9ea6c6
-- title:
--   Finite centered grid: exact mean power and Gaussian tail
-- statement:
--   Let $d\ge2$ be an integer, $t>0$, and $v>0$. Use symbols $x_j=(2j-d+1)t$, $0\le j<d$, and the nearest-symbol decoder. Their exact uniform mean power and conditional symbol errors $p_j$ under additive noise $\xi\sim N(0,v)$ satisfy
--
--   $$
--   \frac1d\sum_{j=0}^{d-1}x_j^2=\frac{d^2-1}{3}t^2,\qquad p_j\le\operatorname{erfc}\left(\frac{t}{\sqrt{2v}}\right).
--   $$
--
--   In particular, for any $P>0$, the choice $t_P=\sqrt{3P}/d$ gives mean power at most $P$ and
--
--   $$
--   p_j\le\operatorname{erfc}\left(\sqrt{\frac{3P}{2d^2v}}\right).
--   $$
--
--   This retains the source's conservative spacing while replacing its explicitly approximate integral power calculation with the exact finite sum. Uniform mean-symbol power alone does not enforce a power bound for every outer-code word.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, PDF p. 10, §VII, (90)–(92): equally spaced classical inner-code Gaussian tail

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix

open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.

open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- PDF p.10, (90)–(92): finite centered-grid power and nearest-decoding tail.
Printed/changed/why: (90) is explicitly an integral approximation; the finite
alphabet has exact power (d^2-1)t^2/3. The source's t=sqrt(3P)/d therefore
satisfies the conservative mean-symbol power inequality. No assertion is made
that every outer-code word meets the block-power constraint. -/
theorem classicalGrid_gaussianTail (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (v : NNReal) (hv : 0 < v) (t : ℝ) (ht : 0 < t) :
    gridMeanPower d t = ((d : ℝ) ^ 2 - 1) * t ^ 2 / 3 ∧
    (∀ y : ℝ, ∀ j : Fin d,
      |y - gridSymbol d t (gridDecode d t y)| ≤ |y - gridSymbol d t j|) ∧
    (∀ j : Fin d, gridSymbolError d t v j ≤
      complementaryErrorFunction (t / Real.sqrt (2 * (v : ℝ)))) ∧
    (∀ P : ℝ, 0 < P →
      let spacing := Real.sqrt (3 * P) / (d : ℝ)
      gridMeanPower d spacing ≤ P ∧
      ∀ j : Fin d, gridSymbolError d spacing v j ≤
        complementaryErrorFunction (Real.sqrt (3 * P / (2 * (d : ℝ) ^ 2 * (v : ℝ))))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P08
