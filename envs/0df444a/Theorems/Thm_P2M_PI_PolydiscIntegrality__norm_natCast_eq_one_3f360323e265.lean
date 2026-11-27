-- Prove2me | Theorems.Thm_P2M_PI_PolydiscIntegrality__norm_natCast_eq_one_3f360323e265
-- name    : P2M_PI_PolydiscIntegrality__norm_natCast_eq_one_3f360323e265
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:43:21.018965+00:00
-- url     : https://prove2.me/theorems/6143c8b4-d579-45ae-8478-da7f4304fc76
-- title:
--   P2 M PI Polydisc Integrality  norm nat Cast eq one 3f360323e265: P2 M PI Polydisc Integrality  norm nat Cast eq one 3f360323e265
-- statement:
--   The P2 M PI Polydisc Integrality  norm nat Cast eq one 3f360323e265 construction uses the P2 M PI Polydisc Integrality  norm nat Cast eq one 3f360323e265 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolydiscIntegrality/Lemmas.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolydiscIntegrality/Lemmas.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_NormPPosLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolydiscIntegrality_Lemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PolydiscIntegrality₂
open Filter Topology
variable {p : ℕ} [Fact p.Prime]

theorem P2M_PI_PolydiscIntegrality__norm_natCast_eq_one_3f360323e265 {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by sorry

alias «PI».«PolydiscIntegrality₂».«norm_natCast_eq_one» := P2M_PI_PolydiscIntegrality__norm_natCast_eq_one_3f360323e265
