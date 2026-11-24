-- Prove2me | Theorems.Thm_PI_StabSplit_UnipW_key
-- name    : PI.StabSplit.UnipW.key
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:06:14.924167+00:00
-- url     : https://prove2.me/theorems/ade3c837-6e44-4f20-8e10-46c9e491f760
-- title:
--   Unip W: key
-- statement:
--   The Unip W construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L204-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerFlagSplitting/NilpotentOrthogonalComplement.lean#L204-L239

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_SubFlag
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_NilpotentOrthogonalComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.StabSplit PI.StabSplit.UnipW

theorem PI.StabSplit.UnipW.key {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hgU : gᴴ * Hpk k r * g = Hpk k r)
    (hperp : ∀ v, perpX k r v → perpX k r (g *ᵥ v)) (hgz : inX k r (g *ᵥ z - z)) :
    ∀ q : ℕ, ∀ v, perpX k r v → (g - 1) ^ q *ᵥ v = 0 → inX k r (g *ᵥ v - v) := by sorry
