-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_kernel
-- name    : PI.UnitaryGroupMassFormula.LCG.ap_kernel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:45:54.901932+00:00
-- url     : https://prove2.me/theorems/aa19fabf-e9a9-53ef-a1e5-e4af4374c65b
-- title:
--   LCG: ap kernel
-- statement:
--   The LCG construction uses the ap kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L258-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean#L258-L295

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.UnitaryGroupMassFormula.LCG.ap_kernel (x y : I.GA) (v : InfinitePlace I.F) (δ : Matrix (Fin I.n) (Fin I.n) I.E) (k : ℕ)
    (u b' : Fin k → Fin I.n → I.E)
    (hu : LinearIndependent I.E (fun c => δ *ᵥ u c))
    (hsp : ∀ z, δ *ᵥ z ∈ Submodule.span I.E (Set.range fun c => δ *ᵥ u c))
    (hb : LinearIndependent I.E b') (hperp : ∀ a, PerpKer I δ (b' a)) :
    ∀ z : Fin I.n → ℂ, (Formalism.REAL.Jm (I.ε v) * colM I y v b')ᴴ *ᵥ z = 0 → amat I x y v δ *ᵥ z = 0 := by sorry
