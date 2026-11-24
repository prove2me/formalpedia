-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
-- name    : P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:22.852797+00:00
-- url     : https://prove2.me/theorems/6b41259d-8121-4d18-b0dc-9954a9682784
-- title:
--   P2 M Formalism Fourier Decay Alt Q Eab Gl W hsq  e5d4b9ac7468: P2 M Formalism Fourier Decay Alt Q Eab Gl W hsq  e5d4b9ac7468
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q Eab Gl W hsq  e5d4b9ac7468 construction uses the P2 M Formalism Fourier Decay Alt Q Eab Gl W hsq  e5d4b9ac7468 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/HpartUnique.lean#L20-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468 (M : Mx k r) : Hpk k r * (Hpk k r * M) = M := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«EabGlW».«hsq'» := P2M_Formalism_FourierDecayAlt_Q_EabGlW_hsq__e5d4b9ac7468
