-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_card_quotient_sumElim_19b0155624ac
-- name    : P2M_GroundTheory_Heights__Heights_HermitianExtension_card_quotient_sumElim_19b0155624ac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:55.127412+00:00
-- url     : https://prove2.me/theorems/16f0e5e3-1573-421d-b463-1568eb5d9be0
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Extension card quotient sum Elim 19b0155624ac: P2 M Ground Theory Heights  Heights Hermitian Extension card quotient sum Elim 19b0155624ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Extension card quotient sum Elim 19b0155624ac construction uses the P2 M Ground Theory Heights  Heights Hermitian Extension card quotient sum Elim 19b0155624ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L148-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L148-L215

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n]

theorem P2M_GroundTheory_Heights__Heights_HermitianExtension_card_quotient_sumElim_19b0155624ac {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs'' : LinearIndependent (𝓞 K) s'') :
    Nat.card (E.carrier ⧸ Submodule.span (𝓞 K) (Set.range (Sum.elim (fun i ↦ X.incl (s' i)) u))) =
      Nat.card (E'.carrier ⧸ Submodule.span (𝓞 K) (Set.range s')) *
        Nat.card (E''.carrier ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianExtension».«card_quotient_sumElim» := P2M_GroundTheory_Heights__Heights_HermitianExtension_card_quotient_sumElim_19b0155624ac
