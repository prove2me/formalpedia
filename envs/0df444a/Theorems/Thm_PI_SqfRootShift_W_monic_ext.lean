-- Prove2me | Theorems.Thm_PI_SqfRootShift_W_monic_ext
-- name    : PI.SqfRootShift.W.monic_ext
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:19.305746+00:00
-- url     : https://prove2.me/theorems/bc14f87e-4904-548e-ac88-0494ca312c33
-- title:
--   W: monic ext
-- statement:
--   The W construction uses the monic ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootShift/CountC.lean#L59-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]

theorem PI.SqfRootShift.W.monic_ext {h1 h2 : (ZMod g)[X]} {m : ℕ} (hm1 : h1.Monic) (hm2 : h2.Monic)
    (hd1 : h1.natDegree = m) (hd2 : h2.natDegree = m)
    (hc : ∀ i < m, h1.coeff i = h2.coeff i) : h1 = h2 := by sorry
