-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_sum_comp_algebraMap_c5de2bfea3bb
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_sum_comp_algebraMap_c5de2bfea3bb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:59.243129+00:00
-- url     : https://prove2.me/theorems/3ae3438a-01a6-4960-bc46-a733ed564a7f
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas sum comp algebra Map c5de2bfea3bb: P2 M Ground Theory Heights  Heights Lattice Lemmas sum comp algebra Map c5de2bfea3bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas sum comp algebra Map c5de2bfea3bb construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas sum comp algebra Map c5de2bfea3bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L75-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_sum_comp_algebraMap_c5de2bfea3bb (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) = Module.finrank K L * ∑ σ : K →+* ℂ, f σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«sum_comp_algebraMap» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_sum_comp_algebraMap_c5de2bfea3bb
