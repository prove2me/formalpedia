-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_torus_coeff_le
-- name    : ReciprocityTheory.MultiplicativeHeights.exists_torus_coeff_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:07.132127+00:00
-- url     : https://prove2.me/theorems/3ff87754-f578-4fc1-ba51-db2b89f88abd
-- title:
--   Multiplicative Heights: exists torus coeff le
-- statement:
--   The Multiplicative Heights construction uses the exists torus coeff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L63-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L63-L125

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
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
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.exists_torus_coeff_le {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ z : ι → ℂ, (∀ i, ‖z i‖ = 1) ∧ ‖coeff s g‖ ≤ ‖eval z g‖ := by sorry
