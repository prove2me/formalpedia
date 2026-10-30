-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P29_typicalSequenceCount
-- name    : QAlgorithms.Papers.Independent.Advance50.P29.typicalSequenceCount
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:12:58.737021+00:00
-- url     : https://prove2.me/theorems/70d78133-4adb-401c-a3b0-fccff8945369
-- title:
--   §7.1 (i), Appendix C: weakly typical sequence count
-- statement:
--   Let $P$ be a probability distribution on a finite nonempty alphabet $L$: $P_i\ge0$ and $\sum_iP_i=1$. Define $H(P)=-\sum_iP_i\log_2P_i$, with $0\log_20=0$. For $w\in L^n$, set $p_w=\prod_tP_{w_t}$ and $T_{\varepsilon,n}=\{w:2^{-n(H(P)+\varepsilon)}\le p_w\le2^{-n(H(P)-\varepsilon)}\}$. For every $\varepsilon>0$ and positive integer $n$,
--
--   $$
--   |T_{\varepsilon,n}|<2^{n(H(P)+\varepsilon)}.
--   $$
--
--   This controls the size of the weakly typical set; zero-probability words cannot belong to its positive probability window.
-- source:
--   A random-coding based proof for the quantum coding theorem, arXiv:0712.2558v1, PDF p. 15, §7.1 (i), Appendix C: weakly typical sequence count

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P29

open QAlgorithms MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification coherentInformation singleUseInformation mixed)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Dependency50.P48 (wordProbability)

open QAlgorithms.Papers.Independent.Bridge50.P43 (tensorDensity)

open scoped Matrix ComplexConjugate ComplexOrder Topology

attribute [local instance] Classical.propDecidable

variable {I J E L : Type} [Fintype I] [DecidableEq I]

variable [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E]

variable [Fintype L] [DecidableEq L]

/-- PDF pp.15,21, §7.1(i): strict cardinality bound for the closed weak-typicality window. -/
theorem typicalSequenceCount [Nonempty L] (P : L → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hsum : ∑ i, P i = 1)
    (epsilon : ℝ) (he : 0 < epsilon) (n : ℕ) (hn : 0 < n) :
    ((weakTypicalWords P epsilon n).card : ℝ) <
      (2 : ℝ) ^ ((n : ℝ) * (shannon P + epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P29

end
