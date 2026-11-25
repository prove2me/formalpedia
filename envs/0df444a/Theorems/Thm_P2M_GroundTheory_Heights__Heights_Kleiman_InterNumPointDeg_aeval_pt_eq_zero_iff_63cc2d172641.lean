-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_eq_zero_iff_63cc2d172641
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_eq_zero_iff_63cc2d172641
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:29:42.20427+00:00
-- url     : https://prove2.me/theorems/2e425d13-f41e-566e-85ac-2acf8ae1f71a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt eq zero iff 63cc2d172641: P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt eq zero iff 63cc2d172641
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt eq zero iff 63cc2d172641 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Point Deg aeval pt eq zero iff 63cc2d172641 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumPointDeg.lean#L66-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_eq_zero_iff_63cc2d172641 (f : Poly k N) : aeval (pt.{u, w} pp) f = 0 ↔ f ∈ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumPointDeg».«aeval_pt_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_eq_zero_iff_63cc2d172641
