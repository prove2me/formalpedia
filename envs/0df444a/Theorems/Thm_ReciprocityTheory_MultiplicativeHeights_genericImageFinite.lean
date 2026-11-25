-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_genericImageFinite
-- name    : ReciprocityTheory.MultiplicativeHeights.genericImageFinite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:05.33617+00:00
-- url     : https://prove2.me/theorems/4536c0e5-f350-4d8d-b485-3e6bfa07febd
-- title:
--   Multiplicative Heights: generic Image Finite
-- statement:
--   The Multiplicative Heights construction uses the generic Image Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GenericImageFinite.lean#L31-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/GenericImageFinite.lean#L31-L113

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

theorem ReciprocityTheory.MultiplicativeHeights.genericImageFinite : FieldOfSStatement := by sorry
