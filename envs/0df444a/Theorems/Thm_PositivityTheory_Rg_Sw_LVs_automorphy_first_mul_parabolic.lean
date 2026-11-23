-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_first_mul_parabolic
-- name    : PositivityTheory.Rg.Sw.LVs.automorphy_first_mul_parabolic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:00.021808+00:00
-- url     : https://prove2.me/theorems/c7dc7608-1f7d-4afa-831d-52fcb1a9938c
-- title:
--   LVs: automorphy first mul parabolic
-- statement:
--   The LVs construction uses the automorphy first mul parabolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L108-L111

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

theorem PositivityTheory.Rg.Sw.LVs.automorphy_first_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by sorry
