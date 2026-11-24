-- Prove2me | Theorems.Thm_PI_ScRefExists_TH_mem_primesG
-- name    : PI.ScRefExists.TH.mem_primesG
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:47.746823+00:00
-- url     : https://prove2.me/theorems/9754169c-dff4-419e-95af-eb2e060dcfde
-- title:
--   TH: mem primes G
-- statement:
--   The TH construction uses the mem primes G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaSeriesExistence.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaSeriesExistence.lean#L25-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaSeriesExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.TH.mem_primesG (g : ℕ) (hg : 1 ≤ g) (P : HeightOneSpectrum (𝓞 I.E)) :
    P ∈ primesG I g hg ↔ (g : 𝓞 I.E) ∈ P.asIdeal := by sorry
