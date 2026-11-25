-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_lmul_lpow_e0b30fd3fd3d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_lmul_lpow_e0b30fd3fd3d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:49.833752+00:00
-- url     : https://prove2.me/theorems/70848e41-ec67-4123-ab1e-5ff822a01191
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs lmul lpow e0b30fd3fd3d: P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs lmul lpow e0b30fd3fd3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs lmul lpow e0b30fd3fd3d construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs lmul lpow e0b30fd3fd3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistPowZeroSub.lean#L35-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_lmul_lpow_e0b30fd3fd3d (G B : Kleiman.SubSystem S x Ω) (G' B' : Fin (N + 1) → Submodule S Ω)
    (hG : ∀ i, x i ≠ 0 → G' i = toIndefiniteRowSideFullHecke G i) (hB : ∀ i, x i ≠ 0 → B' i = toIndefiniteRowSideFullHecke B i) (b : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.secs S x (IndefiniteRowSideFullHecke.Kleiman.lmul S G' (IndefiniteRowSideFullHecke.Kleiman.lpow S B' b)) = (G.twist (B.pow b)).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«secs_lmul_lpow» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_lmul_lpow_e0b30fd3fd3d
