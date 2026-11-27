-- Prove2me | Theorems.Thm_UpperTheory_V_LDataCardLeFinrank_ineImage_le_decImage
-- name    : UpperTheory.V.LDataCardLeFinrank.ineImage_le_decImage
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:23.434803+00:00
-- url     : https://prove2.me/theorems/cc216a71-b7ac-5f19-b15f-1df3e11a90da
-- title:
--   LData Card Le Finrank: ine Image le dec Image
-- statement:
--   The LData Card Le Finrank construction uses the ine Image le dec Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L18-L18

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

theorem UpperTheory.V.LDataCardLeFinrank.ineImage_le_decImage (A : ValuationSubring Ω) : ineImage F l A ≤ decImage F l A := by sorry
