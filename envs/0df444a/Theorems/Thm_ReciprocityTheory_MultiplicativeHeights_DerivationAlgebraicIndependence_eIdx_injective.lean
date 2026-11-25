-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_eIdx_injective
-- name    : ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.eIdx_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:40.728035+00:00
-- url     : https://prove2.me/theorems/1c3b6319-3aaf-4bc5-8d96-12fd23817789
-- title:
--   Derivation Algebraic Independence: e Idx injective
-- statement:
--   The Derivation Algebraic Independence construction uses the e Idx injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsDualDerivations.lean#L219-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsDualDerivations.lean#L219-L223

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

theorem ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.eIdx_injective (D m : ℕ) : Function.Injective (eIdx D m) := by sorry
