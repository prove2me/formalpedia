-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qPrin_low
-- name    : ReciprocityTheory.ChartRestriction.L1.qPrin_low
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:22.710348+00:00
-- url     : https://prove2.me/theorems/0a0434a4-a370-4972-887f-f57b7b333459
-- title:
--   L1: q Prin low
-- statement:
--   The L1 construction uses the q Prin low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModQPrin.lean#L235-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModQPrin.lean#L235-L242

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.qPrin_low (R : Subring ℂ) (N : ℕ) (f : ℍ → ℂ) (hf : IsMF (12 * (N : ℤ)) f)
    (hR : CoeffIn R (qExpansion 1 f)) (n0 : ℕ) (u : ℂ) (hu : u ≠ 0)
    (h0 : ∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0)
    (h1 : PowerSeries.coeff n0 (qExpansion 1 f) = u) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧ P.leadingCoeff = u ∧
      ∀ τ, f τ = DD τ ^ N * P.eval (jT τ) := by sorry
