-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_nagata_ne_of_ne_6af563b4cf77
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_nagata_ne_of_ne_6af563b4cf77
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:31.304457+00:00
-- url     : https://prove2.me/theorems/36136197-b8fb-4fca-a240-6cb879c0bf3d
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of nagata ne of ne 6af563b4cf77: P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of nagata ne of ne 6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of nagata ne of ne 6af563b4cf77 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation degree Of nagata ne of ne 6af563b4cf77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L60-L67

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_nagata_ne_of_ne_6af563b4cf77 (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (nagataEquiv f <| monomial v <| coeff v f).degreeOf 0 ≠
    (nagataEquiv f <| monomial w <| coeff w f).degreeOf 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«degreeOf_nagata_ne_of_ne» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_nagata_ne_of_ne_6af563b4cf77
