-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockPoly_claim
-- name    : ReciprocityTheory.MultiplicativeHeights.blockPoly_claim
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:32.612857+00:00
-- url     : https://prove2.me/theorems/a3c74eb8-8d6a-426e-b5a0-db4e0c17ec92
-- title:
--   Multiplicative Heights: block Poly claim
-- statement:
--   The Multiplicative Heights construction uses the block Poly claim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresB.lean#L26-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresB.lean#L26-L160

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric

theorem ReciprocityTheory.MultiplicativeHeights.blockPoly_claim (hSJ : SJStatement) (n : ℕ) : ∀ (k : ℕ) (a : Fin k → ℕ)
    (F : (Fin k → Fin n → ℂ) → ℂ), BlockPoly k n a F → ∀ z0 : Fin k → UnitSphereC n,
    onSpheres F z0 ≠ 0 →
    Integrable (fun z => Real.log ‖onSpheres F z‖) (Measure.pi fun _ : Fin k => sphereProb n) ∧
      Measure.pi (fun _ : Fin k => sphereProb n) {z | onSpheres F z = 0} = 0 := by sorry
