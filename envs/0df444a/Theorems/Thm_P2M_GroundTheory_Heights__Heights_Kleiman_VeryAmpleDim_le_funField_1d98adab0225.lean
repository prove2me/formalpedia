-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_le_funField_1d98adab0225
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_le_funField_1d98adab0225
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:49.431803+00:00
-- url     : https://prove2.me/theorems/a3e0e717-566f-588e-ae89-9c53248d67b4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim le fun Field 1d98adab0225: P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim le fun Field 1d98adab0225
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim le fun Field 1d98adab0225 construction uses the P2 M Ground Theory Heights  Heights Kleiman Very Ample Dim le fun Field 1d98adab0225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L61-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PVeryAmpleDim.lean#L61-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
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
open MvPolynomial AmpleAffineGen
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_le_funField_1d98adab0225 (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {j₀ : Fin (r + 1)} (hj₀ : h j₀ ≠ 0) :
    funField (k := k) x ≤ funField (k := k) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«VeryAmpleDim».«le_funField» := P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_le_funField_1d98adab0225
