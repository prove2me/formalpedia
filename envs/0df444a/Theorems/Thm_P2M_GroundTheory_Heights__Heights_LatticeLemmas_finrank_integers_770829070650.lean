-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_integers_770829070650
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_integers_770829070650
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:50.805073+00:00
-- url     : https://prove2.me/theorems/462d40af-4ecf-450a-992f-80b17a940445
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas finrank integers 770829070650: P2 M Ground Theory Heights  Heights Lattice Lemmas finrank integers 770829070650
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas finrank integers 770829070650 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas finrank integers 770829070650 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L12-L13

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_integers_770829070650 : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«finrank_integers» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_finrank_integers_770829070650
