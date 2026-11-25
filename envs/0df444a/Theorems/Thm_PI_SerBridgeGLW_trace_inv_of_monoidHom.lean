-- Prove2me | Theorems.Thm_PI_SerBridgeGLW_trace_inv_of_monoidHom
-- name    : PI.SerBridgeGLW.trace_inv_of_monoidHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:03.213705+00:00
-- url     : https://prove2.me/theorems/3bc8af1a-41a2-5f5a-a41d-3683bf6a1244
-- title:
--   Ser Bridge GLW: trace inv of monoid Hom
-- statement:
--   The Ser Bridge GLW construction uses the trace inv of monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/ConjugateCharacterFormula.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/ConjugateCharacterFormula.lean#L9-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ComplexOrder
open PI PI.SerBridgeGLW

theorem PI.SerBridgeGLW.trace_inv_of_monoidHom {G : Type} [Group G] [Fintype G] {n : Type} [Fintype n] [DecidableEq n]
    (M : G →* Matrix n n ℂ) (x : G) : star (trace (M x)) = trace (M x⁻¹) := by sorry
