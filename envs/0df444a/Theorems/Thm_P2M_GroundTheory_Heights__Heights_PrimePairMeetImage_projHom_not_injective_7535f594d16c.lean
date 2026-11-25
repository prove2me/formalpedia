-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_projHom_not_injective_7535f594d16c
-- name    : P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_projHom_not_injective_7535f594d16c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:15:02.743337+00:00
-- url     : https://prove2.me/theorems/4eddf8c4-0528-5fc4-b2fb-6f21bb213423
-- title:
--   P2 M Ground Theory Heights  Heights Prime Pair Meet Image proj Hom not injective 7535f594d16c: P2 M Ground Theory Heights  Heights Prime Pair Meet Image proj Hom not injective 7535f594d16c
-- statement:
--   The P2 M Ground Theory Heights  Heights Prime Pair Meet Image proj Hom not injective 7535f594d16c construction uses the P2 M Ground Theory Heights  Heights Prime Pair Meet Image proj Hom not injective 7535f594d16c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimePairMeetImage.lean#L15-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPrimePairMeetImage.lean#L15-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImageDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBadSetSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimePairMeetImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_projHom_not_injective_7535f594d16c (hF : FiniteFibresDimLe.Statement) {n d : ℕ}
    {Q Q' P : Ideal (MvPolynomial (Fin n) ℂ)} (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hQ' : Q'.IsPrime) (hne : Q ≠ Q') (hfin : ∀ y, (ComplexSets.fibre Q A y).Finite)
    (hfin' : ∀ y, (ComplexSets.fibre Q' A y).Finite) (hP : P.IsPrime) (hle : Q ⊔ Q' ≤ P) :
    ¬ Function.Injective (ComplexSets.projHom P A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PrimePairMeetImage».«projHom_not_injective» := P2M_GroundTheory_Heights__Heights_PrimePairMeetImage_projHom_not_injective_7535f594d16c
