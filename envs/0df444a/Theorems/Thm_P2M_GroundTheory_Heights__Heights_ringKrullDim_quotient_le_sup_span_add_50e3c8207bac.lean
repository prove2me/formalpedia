-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_sup_span_add_50e3c8207bac
-- name    : P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_sup_span_add_50e3c8207bac
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:50.409068+00:00
-- url     : https://prove2.me/theorems/1f69f4c6-ffa0-4ac2-b48a-bd9e291f23fa
-- title:
--   P2 M Ground Theory Heights  Heights ring Krull Dim quotient le sup span add 50e3c8207bac: P2 M Ground Theory Heights  Heights ring Krull Dim quotient le sup span add 50e3c8207bac
-- statement:
--   The P2 M Ground Theory Heights  Heights ring Krull Dim quotient le sup span add 50e3c8207bac construction uses the P2 M Ground Theory Heights  Heights ring Krull Dim quotient le sup span add 50e3c8207bac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimGeneral.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimGeneral.lean#L14-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimGeneral
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
open MvPolynomial Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_sup_span_add_50e3c8207bac {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ringKrullDim_quotient_le_sup_span_add» := P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_sup_span_add_50e3c8207bac
