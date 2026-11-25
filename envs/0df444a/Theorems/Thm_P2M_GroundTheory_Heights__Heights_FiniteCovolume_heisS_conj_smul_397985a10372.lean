-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_conj_smul_397985a10372
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_conj_smul_397985a10372
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:49.925268+00:00
-- url     : https://prove2.me/theorems/d5190115-4c48-48be-91a5-84807eaa6b0e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis S conj smul 397985a10372: P2 M Ground Theory Heights  Heights Finite Covolume heis S conj smul 397985a10372
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis S conj smul 397985a10372 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis S conj smul 397985a10372 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusCoords.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusCoords.lean#L30-L39

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_conj_smul_397985a10372 (α : ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H (starRingEnd ℂ α • y) (Complex.normSq α * t) = (Complex.normSq α : ℂ) * heisS H y t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisS_conj_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_conj_smul_397985a10372
