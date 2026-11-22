-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_TwistData_ldeg_congr__7f80ac31fcf2
-- name    : P2M_Formalism_MainNotions_PlaneGram_TwistData_ldeg_congr__7f80ac31fcf2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:58.848245+00:00
-- url     : https://prove2.me/theorems/e422d907-23ce-4e43-a754-a23cd0e3428d
-- title:
--   P2 M Formalism Main Notions Plane Gram Twist Data ldeg congr  7f80ac31fcf2: P2 M Formalism Main Notions Plane Gram Twist Data ldeg congr  7f80ac31fcf2
-- statement:
--   The P2 M Formalism Main Notions Plane Gram Twist Data ldeg congr  7f80ac31fcf2 construction uses the P2 M Formalism Main Notions Plane Gram Twist Data ldeg congr  7f80ac31fcf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L130-L131

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
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
variable (D : TwistData K)

theorem P2M_Formalism_MainNotions_PlaneGram_TwistData_ldeg_congr__7f80ac31fcf2 {ζ ζ' : D.EM} {i : D.ML} (h : ∀ a, ζ' (i, a) = ζ (i, a)) : ldeg ζ' i = ldeg ζ i := by sorry

alias «Formalism».«MainNotions».«PlaneGram».«TwistData».«ldeg_congr'» := P2M_Formalism_MainNotions_PlaneGram_TwistData_ldeg_congr__7f80ac31fcf2
