-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_minimalPrimes_graphIdeal_sup_86bab7f1292e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_minimalPrimes_graphIdeal_sup_86bab7f1292e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:41:17.376291+00:00
-- url     : https://prove2.me/theorems/261f46e0-088e-5495-8076-aeaf226f9b19
-- title:
--   P2 M Ground Theory Heights  Heights Targets minimal Primes graph Ideal sup 86bab7f1292e: P2 M Ground Theory Heights  Heights Targets minimal Primes graph Ideal sup 86bab7f1292e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets minimal Primes graph Ideal sup 86bab7f1292e construction uses the P2 M Ground Theory Heights  Heights Targets minimal Primes graph Ideal sup 86bab7f1292e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GraphIdeal.lean#L113-L117

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Targets_minimalPrimes_graphIdeal_sup_86bab7f1292e (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).minimalPrimes =
      (fun W => graphIdeal W p) '' (J ⊔ Ideal.span {p}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«minimalPrimes_graphIdeal_sup» := P2M_GroundTheory_Heights__Heights_Targets_minimalPrimes_graphIdeal_sup_86bab7f1292e
