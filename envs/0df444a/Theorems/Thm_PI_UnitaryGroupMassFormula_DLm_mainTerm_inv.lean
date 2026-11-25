-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_mainTerm_inv
-- name    : PI.UnitaryGroupMassFormula.DLm.mainTerm_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:55.028087+00:00
-- url     : https://prove2.me/theorems/8d52476a-4c7e-4733-bdd5-2aee2ca3606f
-- title:
--   DLm: main Term inv
-- statement:
--   The DLm construction uses the main Term inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PDownTop.lean#L40-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PDownTop.lean#L40-L55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PDownTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm
attribute [instance] TopModel.ng TopModel.ns TopModel.cs

theorem PI.UnitaryGroupMassFormula.DLm.mainTerm_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : G.Mat (m + 1 + 1) → V) (D' x : ℂ) :
    G.mainTerm β m (fun _ => 1) Φ x⁻¹ D' =
      ∑ j : Fin (G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).card,
        G.psi β ((((m : ℂ) + 2) * ((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)) * x) •
          ((((m : ℂ) + 2)⁻¹ * ((‖((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)‖ ^
              ((m + 1) ^ 2) : ℝ) : ℂ)) •
            G.OmLong β (m + 1) Φ ((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)) := by sorry
