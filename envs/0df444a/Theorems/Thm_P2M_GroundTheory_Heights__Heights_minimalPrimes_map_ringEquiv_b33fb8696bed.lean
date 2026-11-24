-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed
-- name    : P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:48:12.104383+00:00
-- url     : https://prove2.me/theorems/4d7755ca-8718-4fd0-a386-da873efeb533
-- title:
--   P2 M Ground Theory Heights  Heights minimal Primes map ring Equiv b33fb8696bed: P2 M Ground Theory Heights  Heights minimal Primes map ring Equiv b33fb8696bed
-- statement:
--   The P2 M Ground Theory Heights  Heights minimal Primes map ring Equiv b33fb8696bed construction uses the P2 M Ground Theory Heights  Heights minimal Primes map ring Equiv b33fb8696bed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L39-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')

theorem P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed (I : Ideal A) :
    (I.map σ).minimalPrimes = Ideal.map σ '' I.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«minimalPrimes_map_ringEquiv» := P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed
