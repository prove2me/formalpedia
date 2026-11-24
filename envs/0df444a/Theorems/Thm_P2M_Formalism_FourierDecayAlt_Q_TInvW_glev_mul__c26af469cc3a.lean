-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a
-- name    : P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:57.066487+00:00
-- url     : https://prove2.me/theorems/c7dd745e-caba-48f9-aa29-8b48dc825069
-- title:
--   P2 M Formalism Fourier Decay Alt Q TInv W glev mul  c26af469cc3a: P2 M Formalism Fourier Decay Alt Q TInv W glev mul  c26af469cc3a
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q TInv W glev mul  c26af469cc3a construction uses the P2 M Formalism Fourier Decay Alt Q TInv W glev mul  c26af469cc3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L16-L25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«TInvW».«glev_mul'» := P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a
