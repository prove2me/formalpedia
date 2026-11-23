-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_mul_parabolic
-- name    : PositivityTheory.Rg.Sw.LVs.inverse_first_block_mul_parabolic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:28.042786+00:00
-- url     : https://prove2.me/theorems/1257533d-5d88-4286-ad17-60fdc25b7f09
-- title:
--   LVs: inverse first block mul parabolic
-- statement:
--   The LVs construction uses the inverse first block mul parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L127-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L127-L145

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.inverse_first_block_mul_parabolic {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by sorry
