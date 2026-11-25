-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_scale_8bb1ae9ac553
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_scale_8bb1ae9ac553
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:04:16.214772+00:00
-- url     : https://prove2.me/theorems/b05bd327-20a5-532b-b5b5-bc125dc5ad19
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj scale 8bb1ae9ac553: P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj scale 8bb1ae9ac553
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj scale 8bb1ae9ac553 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Mat conj scale 8bb1ae9ac553 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusCoords.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusCoords.lean#L14-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {a : ι → ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_scale_8bb1ae9ac553 {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) {α : ℂ}
    (hga : g *ᵥ a = α • a) {y : ι → ℂ} (hgy : g *ᵥ y = y) (s : ℂ) :
    g * heisMat H a y s =
      heisMat H a (starRingEnd ℂ α • y) ((Complex.normSq α : ℂ) * s) * g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisMat_conj_scale» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_conj_scale_8bb1ae9ac553
