-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_6_16
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_6_16
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:59:35.459447+00:00
-- url     : https://prove2.me/theorems/d1dc06ee-af0f-428e-bac1-028dd6f717ca
-- title:
--   Example 6.16: a nonprimitive direct sum which is eventually MTD
-- statement:
--   Let $m_1,m_2\ge1$ and let $\tau,\sigma$ be unital primitive channels on $M_{m_1}$ and $M_{m_2}$. Their source direct sum $\phi=\tau\oplus\sigma$ acts separately on the diagonal input blocks and annihilates cross blocks. Then
--   $$\phi\text{ is a unital channel, is eventually MTD, and is not primitive}.$$
--   The two distinct stationary block projections prevent primitivity. This separates eventual MTD from discrete primitivity.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 26, Example 6.16

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 6.16, PDF pp.26. -/
theorem example_6_16 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (t : Map m) (s : Map n) (ht : UnitalChannel t) (hs : UnitalChannel s)
    (hpt : Primitive t) (hps : Primitive s) :
    UnitalChannel (binarySum t s) ∧ Eventually MTD (binarySum t s) ∧
      ¬ Primitive (binarySum t s) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
