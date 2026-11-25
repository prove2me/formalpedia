-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_isIntegralElem_iff_valued_le_one_b8a06fc3e582
-- name    : P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_isIntegralElem_iff_valued_le_one_b8a06fc3e582
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:45:37.416203+00:00
-- url     : https://prove2.me/theorems/6a42435a-d7ba-53b4-a60e-ebb387a19b5c
-- title:
--   P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain is Integral Elem iff valued le one b8a06fc3e582: P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Do
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain is Integral Elem iff valued le one b8a06fc3e582 construction uses the P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain is Integral Elem iff valued le one b8a06fc3e582 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L147-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
open GroundTheory.Global GroundTheory.Global.AdicLiesOver
variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]

theorem P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_isIntegralElem_iff_valued_le_one_b8a06fc3e582 (z : w.adicCompletion K) :
    (completionIntegersTo F v (w.adicCompletion K)).IsIntegralElem z ↔ Valued.v z ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«IntegralPointOfAlgebraicDomain».«isIntegralElem_iff_valued_le_one» := P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_isIntegralElem_iff_valued_le_one_b8a06fc3e582
