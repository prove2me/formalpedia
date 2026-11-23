-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:51.677219+00:00
-- url     : https://prove2.me/theorems/7b29864b-71dc-47da-bce4-355bb7ae2079
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip unitary 881309351cf8: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip unitary 881309351cf8
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip unitary 881309351cf8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi ip unitary 881309351cf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L41-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {κ' : Type*} [Fintype κ']

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8 {H g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) (a b : ι → ℂ) :
    star (g *ᵥ a) ⬝ᵥ (H *ᵥ (g *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«ip_unitary» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_ip_unitary_881309351cf8
