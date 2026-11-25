-- Prove2me | Theorems.Thm_P2M_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint__d38c33bc61b6
-- name    : P2M_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint__d38c33bc61b6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:49.448988+00:00
-- url     : https://prove2.me/theorems/527f0ed2-b06d-435a-b95f-95fa37e44bb8
-- title:
--   P2 M Formalism G0 Tops Choice Probability Lemmas prob and eq mul of disjoint  d38c33bc61b6: P2 M Formalism G0 Tops Choice Probability Lemmas prob and eq mul of disjoint  d38c33bc61b6
-- statement:
--   The P2 M Formalism G0 Tops Choice Probability Lemmas prob and eq mul of disjoint  d38c33bc61b6 construction uses the P2 M Formalism G0 Tops Choice Probability Lemmas prob and eq mul of disjoint  d38c33bc61b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L97-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ChoiceOfTopsRefined.lean#L97-L110

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartA
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTopsRefined
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.G0
open Formalism.G0.TopsChoiceProbabilityLemmas
open TopsConditionalProbabilityWindows

theorem P2M_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint__d38c33bc61b6 {U S R : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) (hR : R ⊆ U) (h : Disjoint S R)
    {A B : Finset ℕ → Prop} (hA : Dep S A) (hB : Dep R B) :
    P U δ (fun t => A t ∧ B t) = P U δ A * P U δ B := by sorry

alias «Formalism».«G0».«TopsChoiceProbabilityLemmas».«prob_and_eq_mul_of_disjoint₂» := P2M_Formalism_G0_TopsChoiceProbabilityLemmas_prob_and_eq_mul_of_disjoint__d38c33bc61b6
