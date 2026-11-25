-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapG_qdet_local
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapG.qdet_local
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:26:12.749138+00:00
-- url     : https://prove2.me/theorems/ceb8da6a-6cf3-5da7-ab5d-d32d086b42b1
-- title:
--   Cap G: qdet local
-- statement:
--   The Cap G construction uses the qdet local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/TopContDiffOn.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/TopContDiffOn.lean#L61-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LholClmEventually
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TopContDiffOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapG
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapG.qdet_local (ε : Fin n → Bool) (Lk : E →L[ℂ] E') {G : Matrix (Fin n) (Fin n) ℂ → E}
    {U W : Set (Matrix (Fin n) (Fin n) ℂ)} {m : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℂ ∞ G U) (hW : IsOpen W) (hWU : ∀ g ∈ W, IsUnit g ∧ g⁻¹ * m ∈ U)
    {f : Matrix (Fin n) (Fin n) ℂ → E'} (hf : ∀ g ∈ W, inUJ ε g → f g = Lk (G (g⁻¹ * m)))
    (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ W) (hgu : inUJ ε g) :
    Formalism.QuantumDeterminants.qdetOp (EabV ε) u f g = Lk (Formalism.QuantumDeterminants.qdetOp negL u G (g⁻¹ * m)) := by sorry
