-- Prove2me | Theorems.Thm_PI_UConjT_submatrix_mem_unitaryGroup
-- name    : PI.UConjT.submatrix_mem_unitaryGroup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:14.636798+00:00
-- url     : https://prove2.me/theorems/8470d08b-b050-558b-923c-095d3d56787e
-- title:
--   UConj T: submatrix mem unitary Group
-- statement:
--   The UConj T construction uses the submatrix mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L47-L56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix

theorem PI.UConjT.submatrix_mem_unitaryGroup {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hk : k ∈ unitaryGroup (Fin (n + 1)) ℂ) (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0) :
    k.submatrix Fin.castSucc Fin.castSucc ∈ unitaryGroup (Fin n) ℂ := by sorry
