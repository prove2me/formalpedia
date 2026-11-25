-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:01:59.445701+00:00
-- url     : https://prove2.me/theorems/0b22367c-eac3-4ed5-9ce5-1a6392f467b8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Is Num Poly LT congr 525cd32145d8: P2 M Ground Theory Heights  Heights Kleiman Is Num Poly LT congr 525cd32145d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Is Num Poly LT congr 525cd32145d8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Is Num Poly LT congr 525cd32145d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L139-L142

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
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
open MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8 {t D : ℕ} {f g : (Fin t → ℕ) → ℤ → ℚ} (h : IsNumPolyLT t D f)
    (hfg : ∀ n c, f n c = g n c) : IsNumPolyLT t D g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«IsNumPolyLT».«congr» := P2M_GroundTheory_Heights__Heights_Kleiman_IsNumPolyLT_congr_525cd32145d8
