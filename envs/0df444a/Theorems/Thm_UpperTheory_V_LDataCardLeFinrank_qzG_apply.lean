-- Prove2me | Theorems.Thm_UpperTheory_V_LDataCardLeFinrank_qzG_apply
-- name    : UpperTheory.V.LDataCardLeFinrank.qzG_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:51.255797+00:00
-- url     : https://prove2.me/theorems/b064efe4-8671-4bd4-bee2-1fcf21c3bec9
-- title:
--   LData Card Le Finrank: qz G apply
-- statement:
--   The LData Card Le Finrank construction uses the qz G apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean#L26-L27

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

theorem UpperTheory.V.LDataCardLeFinrank.qzG_apply (e : ℤ) (g : G F Ω) (x : QZ l) :
    qzG F Ω l e g x = ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x := by sorry
