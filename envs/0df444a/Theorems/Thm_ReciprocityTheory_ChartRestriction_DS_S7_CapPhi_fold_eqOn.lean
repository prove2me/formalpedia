-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_fold_eqOn
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.fold_eqOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:54.494314+00:00
-- url     : https://prove2.me/theorems/c5e5f0e2-5a0d-48f8-8697-4b556d171866
-- title:
--   Cap Phi: fold eq On
-- statement:
--   The Cap Phi construction uses the fold eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L137-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CapPhi.lean#L137-L147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
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
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.fold_eqOn : ∀ (p : ℕ) (T : Fin p → (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (A : Fin p → Module.End ℂ (smoothS n)),
    (∀ i (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (T i F) ((A i G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)) →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn ((List.ofFn T).foldr (fun t h => t h) F)
        ((((List.ofFn A).prod) G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n)
  := by sorry
