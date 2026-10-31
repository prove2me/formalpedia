-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_propagatingNumber_compose
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.propagatingNumber_compose
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:32:36.583141+00:00
-- url     : https://prove2.me/theorems/e3fb2c28-5f4c-45fe-b215-1bb5cb284d81
-- title:
--   Unnumbered (1.3): propagating-number inequality
-- statement:
--   Let $k\ge1$ and let $d,e$ be set partitions of the top and bottom rows of $k$ vertices. Write $d\circ e$ for stacking $d$ above $e$, identifying their middle row, and retaining the induced partition of the outer rows. Let $\operatorname{pn}(d)$ count blocks meeting both rows. Then
--
--   $$\operatorname{pn}(d\circ e)\le\min\{\operatorname{pn}(d),\operatorname{pn}(e)\}.$$
--
--   This is the structural bound underlying the propagating ideal.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 4, Unnumbered (1.3): propagating-number inequality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Propagating number under stacking, PDF p.4, equation (1.3). -/
theorem propagatingNumber_compose (k : ℕ) (_hk : 0 < k) (d e : PartitionDiagram k) :
    propagatingNumber (diagramCompose d e) ≤ min (propagatingNumber d) (propagatingNumber e) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
