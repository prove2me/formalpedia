-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_sum_ge_39d70bd0cb3e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_sum_ge_39d70bd0cb3e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:09.469903+00:00
-- url     : https://prove2.me/theorems/ac9bb3ef-b78b-4246-822f-59ee10158c72
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra sum ge 39d70bd0cb3e: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra sum ge 39d70bd0cb3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra sum ge 39d70bd0cb3e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Top Algebra sum ge 39d70bd0cb3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedTopAlgebra.lean#L20-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedTopAlgebra.lean#L20-L40

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_sum_ge_39d70bd0cb3e (d : ℕ) (m : ℕ → ℝ) (hm : ∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i)
    (Q x : ℝ) (hQ : 0 ≤ Q) (hx : 0 ≤ x) :
    Q * ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i
        + x ^ d * m d ≤
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedTopAlgebra».«sum_ge» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedTopAlgebra_sum_ge_39d70bd0cb3e
