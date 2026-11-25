-- Prove2me | Theorems.Thm_PI_SqPairLocal_glue_fin
-- name    : PI.SqPairLocal.glue_fin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:25:27.023098+00:00
-- url     : https://prove2.me/theorems/08e4a4b7-60a9-45b9-bb11-98780c73cce2
-- title:
--   Sq Pair Local: glue fin
-- statement:
--   The Sq Pair Local construction uses the glue fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L252-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/IsMaximalComapCj.lean#L252-L311

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairLocal.glue_fin (hP : PowLoc) (hO : OnePlace) (hE : PI.IsCMUnram E)
    {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hN : Even N) (h' : IsSDG E N L') (h'' : IsSDG E N L'')
    {c : 𝓞 E} (hc : c ≠ 0) (T : Finset (Ideal (𝓞 E))) (hT : ∀ P ∈ T, P.IsMaximal) :
    ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
      ∀ P ∈ T, Good P c L' L'' e ∧ Good (P.comap (cj E)) c L' L'' e := by sorry
