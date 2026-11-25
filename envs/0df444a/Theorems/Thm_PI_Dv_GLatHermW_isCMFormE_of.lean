-- Prove2me | Theorems.Thm_PI_Dv_GLatHermW_isCMFormE_of
-- name    : PI.Dv.GLatHermW.isCMFormE_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:49.816496+00:00
-- url     : https://prove2.me/theorems/502b197b-2617-4e87-a28e-75f3264500ce
-- title:
--   GLat Herm W: is CMForm E of
-- statement:
--   The GLat Herm W construction uses the is CMForm E of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/IsCMFormEOf.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianGroupLattices/IsCMFormEOf.lean#L68-L79

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

theorem PI.Dv.GLatHermW.isCMFormE_of (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hC : IsCMForm A ρ h) :
    IsCMFormE A (ρ.asAlgebraHom (eG T)) h := by sorry
