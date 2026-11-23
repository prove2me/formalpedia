-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PullUnifHom_le_left__12395fff6ef7
-- name    : P2M_GlobalTheory_PullUnifHom_le_left__12395fff6ef7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:39.242816+00:00
-- url     : https://prove2.me/theorems/773ec126-f61a-4092-8a13-1588ff1549e2
-- title:
--   P2 M Global Theory Pull Unif Hom le left  12395fff6ef7: P2 M Global Theory Pull Unif Hom le left  12395fff6ef7
-- statement:
--   The P2 M Global Theory Pull Unif Hom le left  12395fff6ef7 construction uses the P2 M Global Theory Pull Unif Hom le left  12395fff6ef7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHolUnifPullAlongGroupHom.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHolUnifPullAlongGroupHom.lean#L26-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHolUnifPullAlongGroupHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.PullUnifHom
open GlobalTheory.PullHermitian
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_PullUnifHom_le_left__12395fff6ef7 {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U := by sorry

alias «GlobalTheory».«PullUnifHom».«le_left'» := P2M_GlobalTheory_PullUnifHom_le_left__12395fff6ef7
