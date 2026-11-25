-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_eq_C_of_pderiv_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.eq_C_of_pderiv_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:08.354329+00:00
-- url     : https://prove2.me/theorems/f9637e61-094c-432e-9c72-544e62a1e273
-- title:
--   Log Pf: eq C of pderiv zero
-- statement:
--   The Log Pf construction uses the eq C of pderiv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogChain.lean#L167-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogChain.lean#L167-L188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.FG.SolveVAux
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {σ τ : Type}

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.eq_C_of_pderiv_zero [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv k v g = 0) :
    g = C (constantCoeff g) := by sorry
