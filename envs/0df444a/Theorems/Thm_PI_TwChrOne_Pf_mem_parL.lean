-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_mem_parL
-- name    : PI.TwChrOne.Pf.mem_parL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:08.146702+00:00
-- url     : https://prove2.me/theorems/ae7c0c82-8f7f-4a96-82b8-7b367887d4ed
-- title:
--   Pf: mem par L
-- statement:
--   The Pf construction uses the mem par L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L156-L159

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}
variable {kj N c : ℕ}

theorem PI.TwChrOne.Pf.mem_parL {q : ℕ} {x : Sp E (N + c)} :
    x ∈ LocE.parL P q kj N c ↔
      (fun l : Fin (N + c) => ((q : E) ^ (if kj ≤ l.1 ∧ l.1 < N then (1 : ℤ) else 0))⁻¹ * x l) ∈
        stdAt E (N + c) P := by sorry
