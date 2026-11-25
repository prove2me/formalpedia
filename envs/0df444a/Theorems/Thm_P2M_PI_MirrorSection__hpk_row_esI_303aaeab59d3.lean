-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__hpk_row_esI_303aaeab59d3
-- name    : P2M_PI_MirrorSection__hpk_row_esI_303aaeab59d3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:57:31.125182+00:00
-- url     : https://prove2.me/theorems/655097bb-133e-4cf1-a5df-394c51c836f3
-- title:
--   P2 M PI Mirror Section  hpk row es I 303aaeab59d3: P2 M PI Mirror Section  hpk row es I 303aaeab59d3
-- statement:
--   The P2 M PI Mirror Section  hpk row es I 303aaeab59d3 construction uses the P2 M PI Mirror Section  hpk row es I 303aaeab59d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L178-L181

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}

theorem P2M_PI_MirrorSection__hpk_row_esI_303aaeab59d3 (b : Fin r) (l : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) l = if l = eI k r b then 1 else 0 := by sorry

alias «PI».«MirrorSection₂».«hpk_row_esI» := P2M_PI_MirrorSection__hpk_row_esI_303aaeab59d3
