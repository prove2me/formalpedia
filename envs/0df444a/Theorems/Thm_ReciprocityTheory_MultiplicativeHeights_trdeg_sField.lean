-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_trdeg_sField
-- name    : ReciprocityTheory.MultiplicativeHeights.trdeg_sField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:16.150647+00:00
-- url     : https://prove2.me/theorems/f0a3e128-2b1c-4642-acc3-5557bcd8f8b0
-- title:
--   Multiplicative Heights: trdeg s Field
-- statement:
--   The Multiplicative Heights construction uses the trdeg s Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GenericImageFinite.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GenericImageFinite.lean#L9-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_GenericImageFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial DerivationAlgebraicIndependence

theorem ReciprocityTheory.MultiplicativeHeights.trdeg_sField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ) :
    Algebra.trdeg K (SField Ω D m) = Algebra.trdeg K Ω + ((1 + (D + 1) * m : ℕ) : Cardinal) := by sorry
