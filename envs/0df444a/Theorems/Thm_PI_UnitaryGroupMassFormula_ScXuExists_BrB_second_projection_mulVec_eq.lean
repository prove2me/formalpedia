-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_second_projection_mulVec_eq
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrB.second_projection_mulVec_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:41:23.418852+00:00
-- url     : https://prove2.me/theorems/01db7292-a1c8-407f-913d-27f1e41029f7
-- title:
--   Br B: second projection mul Vec eq
-- statement:
--   The Br B construction uses the second projection mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean#L57-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean#L57-L84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrB.second_projection_mulVec_eq {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap) (J : Matrix n n R)
    (hdet : IsUnit J.det) (y : Formalism.UG.UJ σ J) (β β' : n → k)
    (h : β' ᵥ* J.map (SplitGL.p1 π) =
      (β ᵥ* J.map (SplitGL.p1 π)) ᵥ* (((SplitGL.proj σ π J y)⁻¹ : GL n k) : Matrix n n k)) :
    ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) *ᵥ β = β' := by sorry
