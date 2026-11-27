-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Diag_torsionIso_inv___935a2dfbddaa
-- name    : P2M_GlobalTheory_Diag_torsionIso_inv___935a2dfbddaa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:31.66018+00:00
-- url     : https://prove2.me/theorems/077c2ed6-e360-59d1-9c92-dbf75f77074f
-- title:
--   P2 M Global Theory Diag torsion Iso inv   935a2dfbddaa: P2 M Global Theory Diag torsion Iso inv   935a2dfbddaa
-- statement:
--   The P2 M Global Theory Diag torsion Iso inv   935a2dfbddaa construction uses the P2 M Global Theory Diag torsion Iso inv   935a2dfbddaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean#L260-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory GlobalTheory.Diag
variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

theorem P2M_GlobalTheory_Diag_torsionIso_inv___935a2dfbddaa (n : ℕ) : (torsionIso S X n).inv ≫ torsion.ι _ n =
    diagMap S (QuotientAddGroup.mk' (nsmulAddMonoidHom n : X →+ X).range) := by sorry

alias «GlobalTheory».«Diag».«torsionIso_inv_ι» := P2M_GlobalTheory_Diag_torsionIso_inv___935a2dfbddaa
