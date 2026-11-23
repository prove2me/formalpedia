-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm
-- name    : ReciprocityTheory.PTheta.dot_mulVec_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:07.856657+00:00
-- url     : https://prove2.me/theorems/c4274e6a-3bf6-45e3-b869-4e4999b34e8d
-- title:
--   PTheta: dot mul Vec symm
-- statement:
--   The PTheta construction uses the dot mul Vec symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Transl.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/Transl.lean#L30-L32

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.PTheta.dot_mulVec_symm {τ : Matrix ι ι ℂ} (hτ : τ.IsSymm) (s w : ι → ℂ) :
    w ⬝ᵥ (τ *ᵥ s) = s ⬝ᵥ (τ *ᵥ w) := by sorry
