-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_hypH__461b564647c2
-- name    : P2M_Formalism_MainNotions_PlaneGram_TwistData_hypH__461b564647c2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:12.621575+00:00
-- url     : https://prove2.me/theorems/e2644bf1-84fc-42f3-9dc1-e575682079ab
-- title:
--   P2 M Formalism Main Notions Plane Gram Twist Data hyp H  461b564647c2: P2 M Formalism Main Notions Plane Gram Twist Data hyp H  461b564647c2
-- statement:
--   The P2 M Formalism Main Notions Plane Gram Twist Data hyp H  461b564647c2 construction uses the P2 M Formalism Main Notions Plane Gram Twist Data hyp H  461b564647c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L265-L270

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}

theorem P2M_Formalism_MainNotions_PlaneGram_TwistData_hypH__461b564647c2 (D : TwistData K) (p : ℕ) (kH : ℝ) (hH : D.HypH p kH) (j : Fin D.J) (m : Fin D.r)
    (i : Fin (D.nch j)) :
    (D.r : ℝ) * D.dLL (D.aux₃ j) / (D.P p (D.aux₃ j, m) : ℝ) + kH * D.r * D.c ≤ D.sl j i := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«TwistData».«hypH'» := P2M_Formalism_MainNotions_PlaneGram_TwistData_hypH__461b564647c2
