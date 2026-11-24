-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04
-- name    : P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:18:27.588905+00:00
-- url     : https://prove2.me/theorems/b75d7d55-6426-49e3-aa1f-711ecb8cfb2d
-- title:
--   P2 M Formalism Fourier Decay Alt Q TInv W glev row  71270a473e04: P2 M Formalism Fourier Decay Alt Q TInv W glev row  71270a473e04
-- statement:
--   The P2 M Formalism Fourier Decay Alt Q TInv W glev row  71270a473e04 construction uses the P2 M Formalism Fourier Decay Alt Q TInv W glev row  71270a473e04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/TransferInvarianceRestriction.lean#L146-L149

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

theorem P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04 {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q p : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g q p = bvec p q := by sorry

alias «Formalism».«FourierDecayAlt».«Q».«TInvW».«glev_row'» := P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04
