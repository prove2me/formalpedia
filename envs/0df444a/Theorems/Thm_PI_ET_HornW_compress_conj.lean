-- Prove2me | Theorems.Thm_PI_ET_HornW_compress_conj
-- name    : PI.ET.HornW.compress_conj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:44.361547+00:00
-- url     : https://prove2.me/theorems/ecfa7684-26c3-5680-a946-06c1a07344d6
-- title:
--   Horn W: compress conj
-- statement:
--   The Horn W construction uses the compress conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L89-L97

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

theorem PI.ET.HornW.compress_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ) {k : ℕ}
    (hk : k ≤ n) (f : Fin n → ℂ) :
    (W * emb hk)ᴴ * (W * diagonal f * Wᴴ) * (W * emb hk) =
      diagonal (fun i => f (Fin.castLE hk i)) := by sorry
