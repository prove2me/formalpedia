-- Prove2me | Theorems.Thm_PI_ET_HornW_emb_compress
-- name    : PI.ET.HornW.emb_compress
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:22.547002+00:00
-- url     : https://prove2.me/theorems/500e8c59-1faa-4c0b-9197-983ddd9db509
-- title:
--   Horn W: emb compress
-- statement:
--   The Horn W construction uses the emb compress property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L76-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}

theorem PI.ET.HornW.emb_compress {k : ℕ} (hk : k ≤ n) (f : Fin n → ℂ) :
    (emb hk)ᴴ * diagonal f * emb hk = diagonal (fun i => f (Fin.castLE hk i)) := by sorry
