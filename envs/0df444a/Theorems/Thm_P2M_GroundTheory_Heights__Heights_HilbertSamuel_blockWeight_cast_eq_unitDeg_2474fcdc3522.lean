-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_blockWeight_cast_eq_unitDeg_2474fcdc3522
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_blockWeight_cast_eq_unitDeg_2474fcdc3522
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:35.744515+00:00
-- url     : https://prove2.me/theorems/fdf66dee-3d85-58e2-8add-b297ff2e42b1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel block Weight cast eq unit Deg 2474fcdc3522: P2 M Ground Theory Heights  Heights Hilbert Samuel block Weight cast eq unit Deg 2474fcdc3522
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel block Weight cast eq unit Deg 2474fcdc3522 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel block Weight cast eq unit Deg 2474fcdc3522 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIntersectionRecursion.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIntersectionRecursion.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_blockWeight_cast_eq_unitDeg_2474fcdc3522 {K : Type} [DecidableEq K] (ι : K → Type) (b : K) (i : ι b) :
    (fun k => ((blockWeight ι ⟨b, i⟩ k : ℕ) : ℤ)) = unitDeg b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«blockWeight_cast_eq_unitDeg» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_blockWeight_cast_eq_unitDeg_2474fcdc3522
