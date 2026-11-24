-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__col_eq_524aef35e814
-- name    : P2M_PI_MirrorSection__col_eq_524aef35e814
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:56:46.578537+00:00
-- url     : https://prove2.me/theorems/043c4207-61b9-4e9b-9376-31f2db939e17
-- title:
--   P2 M PI Mirror Section  col eq 524aef35e814: P2 M PI Mirror Section  col eq 524aef35e814
-- statement:
--   The P2 M PI Mirror Section  col eq 524aef35e814 construction uses the P2 M PI Mirror Section  col eq 524aef35e814 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/HpkRowEsI.lean#L54-L56

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

theorem P2M_PI_MirrorSection__col_eq_524aef35e814 (g : B.Mat k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by sorry

alias «PI».«MirrorSection₂».«col_eq» := P2M_PI_MirrorSection__col_eq_524aef35e814
