-- Prove2me | Theorems.Thm_P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3
-- name    : P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:06.112857+00:00
-- url     : https://prove2.me/theorems/bfdf1160-b456-4754-ad3f-432faea5e8c7
-- title:
--   P2 M Formalism Graded Weyl Divisibility support X subset  c6434ddb5fe3: P2 M Formalism Graded Weyl Divisibility support X subset  c6434ddb5fe3
-- statement:
--   The P2 M Formalism Graded Weyl Divisibility support X subset  c6434ddb5fe3 construction uses the P2 M Formalism Graded Weyl Divisibility support X subset  c6434ddb5fe3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LBidetdomLemmas.lean#L98-L100

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3 {σ R : Type*} [CommSemiring R] (v : σ) :
    (X v : MvPolynomial σ R).support ⊆ {Finsupp.single v 1} := by sorry

alias «Formalism».«GradedWeylDivisibility».«support_X_subset'» := P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3
