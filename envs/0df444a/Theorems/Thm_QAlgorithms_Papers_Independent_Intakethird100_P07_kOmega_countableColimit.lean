-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kOmega_countableColimit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_countableColimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:30:33.951273+00:00
-- url     : https://prove2.me/theorems/72d86524-8c90-4580-a6ad-07ea8662ea75
-- title:
--   Proposition C.5
-- statement:
--   Let $F:J\to\mathrm{Top}$ be a small diagram with at most countably many objects and morphisms, each of whose objects is k-omega in the sense of Definition C.1. Then its colimit in Top satisfies
--
--   $$\operatorname{colim}_{j\in J}F(j)\text{ is k-omega}.$$
--
--   This includes finite and countable colimits, with the empty colimit allowed. The topology is the actual categorical colimit topology, without Hausdorff reflection.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 38, Proposition C.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Proposition C.5, PDF p. 38: countable colimits in Top are k-omega
when every object is k-omega. Countability concerns both objects and morphisms;
finite and empty diagrams are included. -/
theorem kOmega_countableColimit
    (J : Type u) [SmallCategory J] [Countable J]
    [Countable (Σ i : J, Σ j : J, (i ⟶ j))] (F : J ⥤ TopCat.{u})
    (hF : ∀ j, IsKOmega (F.obj j)) :
    IsKOmega (Limits.colimit F : TopCat.{u}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
