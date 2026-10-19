-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_6_13
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_6_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:58:31.935982+00:00
-- url     : https://prove2.me/theorems/1774f4b1-be77-4810-ac91-1b1636fadb83
-- title:
--   Remark 6.13: minimal convex unitary-invariant absorbing set
-- statement:
--   Let $d\ge1$, and write $\operatorname{EEB}(d)$ for the eventually EB unital channels. A subset $S$ is absorbing if every $\tau\in\operatorname{EEB}(d)$ has all sufficiently large positive powers in $S$. Then $\operatorname{MTD}(d)\subseteq\operatorname{EEB}(d)$ is absorbing, convex, and closed under unitary-channel composition on both sides. Moreover,
--   $$\operatorname{MTD}(d)\subseteq S$$
--   for every absorbing convex $S\subseteq\operatorname{EEB}(d)$ with that unitary closure. This is minimality by inclusion, not uniqueness of every absorbing set.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 25, Remark 6.13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 6.13, PDF pp.25. -/
theorem remark_6_13 {d : ℕ} (hd : 0 < d) :
    ({t : Map d | MTD t} ⊆ EEB d) ∧
    Absorbing {t : Map d | MTD t} ∧ Convex ℝ {t : Map d | MTD t} ∧
    UnitaryClosed {t : Map d | MTD t} ∧
    (∀ S : Set (Map d), S ⊆ EEB d → Absorbing S → Convex ℝ S → UnitaryClosed S →
      {t : Map d | MTD t} ⊆ S) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
