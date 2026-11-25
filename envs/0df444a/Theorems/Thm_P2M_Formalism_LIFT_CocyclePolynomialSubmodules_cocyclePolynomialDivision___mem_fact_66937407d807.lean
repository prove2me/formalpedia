-- Prove2me | Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules_cocyclePolynomialDivision___mem_fact_66937407d807
-- name    : P2M_Formalism_LIFT_CocyclePolynomialSubmodules_cocyclePolynomialDivision___mem_fact_66937407d807
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:44.050802+00:00
-- url     : https://prove2.me/theorems/41cb40e1-f994-4546-8c17-5468be66d20a
-- title:
--   P2 M Formalism LIFT Cocycle Polynomial Submodules cocycle Polynomial Division   mem fact 66937407d807: P2 M Formalism LIFT Cocycle Polynomial Submodules cocycle Polynomial Division   mem fact 66937407
-- statement:
--   The P2 M Formalism LIFT Cocycle Polynomial Submodules cocycle Polynomial Division   mem fact 66937407d807 construction uses the P2 M Formalism LIFT Cocycle Polynomial Submodules cocycle Polynomial Division   mem fact 66937407d807 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean#L103-L106

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)

theorem P2M_Formalism_LIFT_CocyclePolynomialSubmodules_cocyclePolynomialDivision___mem_fact_66937407d807 {n : D} (hn : n ∈ W.N) : W.φ (B.X ^ (M + 1) • n) ∈ W.N := by sorry

alias «Formalism».«LIFT».«CocyclePolynomialSubmodules».«cocyclePolynomialDivision_φ_mem_fact» := P2M_Formalism_LIFT_CocyclePolynomialSubmodules_cocyclePolynomialDivision___mem_fact_66937407d807
