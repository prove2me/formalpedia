-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_local
-- name    : ReciprocityTheory.L2DbarEstimates.I.sh_local
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:58.262555+00:00
-- url     : https://prove2.me/theorems/5be5c533-ae26-41fe-9bc8-520220fd892c
-- title:
--   I: sh local
-- statement:
--   The I construction uses the sh local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L59-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L59-L106

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.sh_local {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (p : M) (hp : p ∈ zeroSet n g)
    (hJ : jac n z g p ≠ 0) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (hpe : p ∈ e.source) :
    ∃ ρ > 0, ball (e p) ρ ⊆ e.target ∧ InjOn (shG n g e.symm) (ball (e p) ρ) ∧
      ∀ ρ' > 0, ∃ κ > 0, ∀ y ∈ ball (e p) ρ, ‖shG n g e.symm y‖ < κ → y ∈ ball (e p) ρ' := by sorry
