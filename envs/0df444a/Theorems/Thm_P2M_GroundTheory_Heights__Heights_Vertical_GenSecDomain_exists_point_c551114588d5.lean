-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_exists_point_c551114588d5
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_exists_point_c551114588d5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:42.563667+00:00
-- url     : https://prove2.me/theorems/cb134958-2d07-4d42-8fbb-65de619d53a4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain exists point c551114588d5: P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain exists point c551114588d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain exists point c551114588d5 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Domain exists point c551114588d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L156-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecDomain.lean#L156-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_exists_point_c551114588d5 (h₂ : IncidenceGeneric.Statement) (h₃ : IncIdealBelow.Statement)
    (Q : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (hQ : IsProjPrime Q) (hg : IsChowForm Q (e + 1) g) :
    ∃ (Ω : Type) (_ : Field Ω) (Ψ : SecR Q e →+* Ω),
      Function.Injective (Ψ.comp (algebraMap (MvPolynomial (Par e n) k) (SecR Q e))) ∧
        ∀ l, X l ∉ Q → Ψ (xc Q e l) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecDomain».«exists_point» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_exists_point_c551114588d5
