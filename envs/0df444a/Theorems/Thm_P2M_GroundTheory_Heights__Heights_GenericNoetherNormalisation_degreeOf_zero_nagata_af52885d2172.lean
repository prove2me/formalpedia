-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_zero_nagata_af52885d2172
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_zero_nagata_af52885d2172
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:08.18061+00:00
-- url     : https://prove2.me/theorems/221d1469-fea3-4058-b6e6-a48ff74e06b6
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of zero nagata af52885d2172: P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of zero nagata af52885d21
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of zero nagata af52885d2172 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of zero nagata af52885d2172 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L44-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_zero_nagata_af52885d2172 {a : A} (ha : a ≠ 0) : ((nagataEquiv f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«degreeOf_zero_nagata» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_zero_nagata_af52885d2172
