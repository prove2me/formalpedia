-- Prove2me | Theorems.Thm_P2M_PI_FockOneDegW_Diag_omAct_apply__14bba05dafb0
-- name    : P2M_PI_FockOneDegW_Diag_omAct_apply__14bba05dafb0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:56:20.343467+00:00
-- url     : https://prove2.me/theorems/072de09d-fc7d-4b16-a162-295023d088d5
-- title:
--   P2 M PI Fock One Deg W Diag om Act apply  14bba05dafb0: P2 M PI Fock One Deg W Diag om Act apply  14bba05dafb0
-- statement:
--   The P2 M PI Fock One Deg W Diag om Act apply  14bba05dafb0 construction uses the P2 M PI Fock One Deg W Diag om Act apply  14bba05dafb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/OmEDiagMonomial.lean#L51-L54

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

theorem P2M_PI_FockOneDegW_Diag_omAct_apply__14bba05dafb0 (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by sorry

alias «PI».«FockOneDegW».«Diag».«omAct_apply'» := P2M_PI_FockOneDegW_Diag_omAct_apply__14bba05dafb0
