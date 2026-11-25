-- Prove2me | Theorems.Thm_PI_Dv_GLatHermW_isCM_sum
-- name    : PI.Dv.GLatHermW.isCM_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:27.576271+00:00
-- url     : https://prove2.me/theorems/41b17f37-3a44-497f-828d-c08eb3e07a46
-- title:
--   GLat Herm W: is CM sum
-- statement:
--   The GLat Herm W construction uses the is CM sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/IsCMFormEOf.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/IsCMFormEOf.lean#L34-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLatHermW.isCM_sum {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsCM (f i)) :
    IsCM (∑ i ∈ s, f i) := by sorry
