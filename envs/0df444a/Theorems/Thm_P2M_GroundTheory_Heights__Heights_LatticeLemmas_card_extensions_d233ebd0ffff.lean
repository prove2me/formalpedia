-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_extensions_d233ebd0ffff
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_extensions_d233ebd0ffff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:48.913268+00:00
-- url     : https://prove2.me/theorems/a6985b72-6ed1-4e17-8a3d-38d12cca61e0
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas card extensions d233ebd0ffff: P2 M Ground Theory Heights  Heights Lattice Lemmas card extensions d233ebd0ffff
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas card extensions d233ebd0ffff construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas card extensions d233ebd0ffff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/BaseChangeIndex.lean#L63-L73

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

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_extensions_d233ebd0ffff (σ : K →+* ℂ) :
    Nat.card {τ : L →+* ℂ // τ.comp (algebraMap K L) = σ} = Module.finrank K L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«card_extensions» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_extensions_d233ebd0ffff
