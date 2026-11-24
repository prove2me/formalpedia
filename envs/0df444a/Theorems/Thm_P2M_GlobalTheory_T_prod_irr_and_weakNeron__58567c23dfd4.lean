-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_prod_irr_and_weakNeron__58567c23dfd4
-- name    : P2M_GlobalTheory_T_prod_irr_and_weakNeron__58567c23dfd4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:29.868341+00:00
-- url     : https://prove2.me/theorems/6d9a2583-9bc1-498b-8e01-4e3a2ae251ac
-- title:
--   P2 M Global Theory T prod irr and weak Neron  58567c23dfd4: P2 M Global Theory T prod irr and weak Neron  58567c23dfd4
-- statement:
--   The P2 M Global Theory T prod irr and weak Neron  58567c23dfd4 construction uses the P2 M Global Theory T prod irr and weak Neron  58567c23dfd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ProdIrrAndWeakNeronStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ProdIrrAndWeakNeronStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_prod_irr_and_weakNeron__58567c23dfd4 : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' : Over (Sp K)), (∀ (M : Model R A) (N : Model R A'), M.Irr → N.Irr → (M.prod N).Irr) ∧ ∀ (I I' : Type) (M : I → Model R A) (N : I' → Model R A'), WeakNeron M → WeakNeron N → WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by sorry

alias «GlobalTheory».«T».«prod_irr_and_weakNeron'» := P2M_GlobalTheory_T_prod_irr_and_weakNeron__58567c23dfd4
