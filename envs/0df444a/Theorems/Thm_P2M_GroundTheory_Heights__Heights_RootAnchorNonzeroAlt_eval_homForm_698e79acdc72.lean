-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_eval_homForm_698e79acdc72
-- name    : P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_eval_homForm_698e79acdc72
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:48.710731+00:00
-- url     : https://prove2.me/theorems/7f87c0d9-f200-4cda-9954-040896dcd822
-- title:
--   P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt eval hom Form 698e79acdc72: P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt eval hom Form 698e79acdc72
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt eval hom Form 698e79acdc72 construction uses the P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt eval hom Form 698e79acdc72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L65-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt

theorem P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_eval_homForm_698e79acdc72 {f j m : ℕ} {q : Polynomial ℤ} (hq : q.Monic) {τ : Fin f} {I : PlIdx j m}
    {z : (Σ _ : Fin f, PlIdx j m) → ℂ} (hz : z ⟨τ, plAnchor j m⟩ = 0) :
    eval z (map (Int.castRingHom ℂ) (homForm q τ I)) = z ⟨τ, I⟩ ^ q.natDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootAnchorNonzeroAlt».«eval_homForm» := P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_eval_homForm_698e79acdc72
