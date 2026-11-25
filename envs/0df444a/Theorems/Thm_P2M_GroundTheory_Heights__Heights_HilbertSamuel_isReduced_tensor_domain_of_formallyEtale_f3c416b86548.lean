-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_formallyEtale_f3c416b86548
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_formallyEtale_f3c416b86548
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:11.832033+00:00
-- url     : https://prove2.me/theorems/c146d880-5339-4a56-b93c-c42e4419775c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of formally Etale f3c416b86548: P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of formally Etal
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of formally Etale f3c416b86548 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of formally Etale f3c416b86548 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeComplexRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial TensorProduct
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_formallyEtale_f3c416b86548 (E L D : Type*) [Field E] [Field L] [Algebra E L]
    [Algebra.FormallyEtale E L] [Algebra.EssFiniteType E L] [CommRing D] [IsDomain D]
    [Algebra E D] : IsReduced (L ⊗[E] D) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isReduced_tensor_domain_of_formallyEtale» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_formallyEtale_f3c416b86548
