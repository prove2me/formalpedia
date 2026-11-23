-- Prove2me | Theorems.Thm_PI_IsoDerivBFintype_cauchyBinet
-- name    : PI.IsoDerivBFintype.cauchyBinet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:49.626584+00:00
-- url     : https://prove2.me/theorems/214852a9-090d-43df-ba64-f4fe43ff69d5
-- title:
--   Iso Deriv BFintype: cauchy Binet
-- statement:
--   The Iso Deriv BFintype construction uses the cauchy Binet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ExistsOePerm.lean#L33-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDerivative/ExistsOePerm.lean#L33-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
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
open PI PI.IsoDerivBFintype

theorem PI.IsoDerivBFintype.cauchyBinet {R : Type*} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by sorry
