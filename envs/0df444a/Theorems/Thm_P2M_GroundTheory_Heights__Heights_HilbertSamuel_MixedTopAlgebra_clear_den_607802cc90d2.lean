-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_clear_den_607802cc90d2
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_clear_den_607802cc90d2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:08.523856+00:00
-- url     : https://prove2.me/theorems/01fc9d34-be0b-48e4-bf86-93fc175c4694
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra clear den 607802cc90d2: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra clear den 607802cc90d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra clear den 607802cc90d2 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra clear den 607802cc90d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedTopAlgebra.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedTopAlgebra.lean#L10-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMixedTopAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonnegAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedTopAlgebra
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
open Filter Polynomial

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_clear_den_607802cc90d2 (d : ℕ) (m : ℕ → ℝ) (Q x : ℝ) (hQ : Q ≠ 0) :
    Q ^ d * ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * (x / Q) ^ i =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedTopAlgebra».«clear_den» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_clear_den_607802cc90d2
