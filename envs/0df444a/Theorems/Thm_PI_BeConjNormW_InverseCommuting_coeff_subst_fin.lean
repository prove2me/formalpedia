-- Prove2me | Theorems.Thm_PI_BeConjNormW_InverseCommuting_coeff_subst_fin
-- name    : PI.BeConjNormW.InverseCommuting.coeff_subst_fin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:34.23131+00:00
-- url     : https://prove2.me/theorems/474d4c10-1145-5ec2-a61d-44488df6e7e0
-- title:
--   Inverse Commuting: coeff subst fin
-- statement:
--   The Inverse Commuting construction uses the coeff subst fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/MemIntegerRingIffNormLeOne.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/MemIntegerRingIffNormLeOne.lean#L46-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_MemIntegerRingIffNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical PowerSeries
open PI PI.BeConjNormW
open PI.BeConjNormW.InverseCommuting
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeConjNormW.InverseCommuting.coeff_subst_fin {f g : PowerSeries ℂ_[p]} (hf0 : constantCoeff f = 0) (n : ℕ) :
    coeff n (subst f g) = ∑ k ∈ Finset.range (n + 1), coeff k g * coeff n (f ^ k) := by sorry
