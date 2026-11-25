-- Prove2me | Theorems.Thm_UpperTheory_V_LDataCardLeFinrank_qzTw_comp_toGS
-- name    : UpperTheory.V.LDataCardLeFinrank.qzTw_comp_toGS
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:08.508507+00:00
-- url     : https://prove2.me/theorems/9a67242c-b4c5-417b-85d7-ea58d5ce4dc9
-- title:
--   LData Card Le Finrank: qz Tw comp to GS
-- statement:
--   The LData Card Le Finrank construction uses the qz Tw comp to GS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L29-L31

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
open UpperTheory UpperTheory.V UpperTheory.V.LDataCardLeFinrank
variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
variable {F l}

theorem UpperTheory.V.LDataCardLeFinrank.qzTw_comp_toGS (D : LData F Ω l) (e : ℤ) : (qzTw D e).comp (toGS Ω _) = qzG F Ω l e := by sorry
