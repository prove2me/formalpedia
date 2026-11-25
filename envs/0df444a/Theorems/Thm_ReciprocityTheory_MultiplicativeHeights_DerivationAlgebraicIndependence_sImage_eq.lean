-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_sImage_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.sImage_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:30.396301+00:00
-- url     : https://prove2.me/theorems/68061844-d676-4d97-8ffe-417fb1cc3305
-- title:
--   Derivation Algebraic Independence: s Image eq
-- statement:
--   The Derivation Algebraic Independence construction uses the s Image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsDualDerivations.lean#L225-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsDualDerivations.lean#L225-L230

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.sImage_eq {Ω : Type} [Field Ω] {D m : ℕ} (x : Fin m → Ω) (p : Fin (D + 1) × Fin (m + 1)) :
    sImage (D := D) x p =
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (gFam x (eIdx D m p)) := by sorry
