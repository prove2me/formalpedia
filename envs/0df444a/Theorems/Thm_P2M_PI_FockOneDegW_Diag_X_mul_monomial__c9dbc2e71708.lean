-- Prove2me | Theorems.Thm_P2M_PI_FockOneDegW_Diag_X_mul_monomial__c9dbc2e71708
-- name    : P2M_PI_FockOneDegW_Diag_X_mul_monomial__c9dbc2e71708
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:17.599316+00:00
-- url     : https://prove2.me/theorems/8b56ece6-7094-4cd7-9c93-634569a7b6c5
-- title:
--   P2 M PI Fock One Deg W Diag X mul monomial  c9dbc2e71708: P2 M PI Fock One Deg W Diag X mul monomial  c9dbc2e71708
-- statement:
--   The P2 M PI Fock One Deg W Diag X mul monomial  c9dbc2e71708 construction uses the P2 M PI Fock One Deg W Diag X mul monomial  c9dbc2e71708 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L12-L15

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag

theorem P2M_PI_FockOneDegW_Diag_X_mul_monomial__c9dbc2e71708 {σ : Type*} (l : σ) (β : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.X l * MvPolynomial.monomial β c =
      MvPolynomial.monomial (Finsupp.single l 1 + β) c := by sorry

alias «PI».«FockOneDegW».«Diag».«X_mul_monomial'» := P2M_PI_FockOneDegW_Diag_X_mul_monomial__c9dbc2e71708
