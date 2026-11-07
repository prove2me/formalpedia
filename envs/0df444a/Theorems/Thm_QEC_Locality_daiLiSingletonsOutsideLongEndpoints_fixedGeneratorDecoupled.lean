-- Prove2me | Theorems.Thm_QEC_Locality_daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
-- name    : QEC.Locality.daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:05:29.757633+00:00
-- url     : https://prove2.me/theorems/be986242-55c5-4423-9c6e-ebd34c1139f6
-- title:
--   Locality: dai Li Singletons Outside Long Endpoints fixed Generator Decoupled
-- statement:
--   Distinct singleton pieces outside the actual long-endpoint set are
--   fixed-generator decoupled in the `ell < 1` source corner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L126-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/LargeDistanceSeparator.lean#L126-L146

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.daiLiSingletonsOutsideLongEndpoints_fixedGeneratorDecoupled
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) {threshold : ℝ}
    (hThreshold : threshold < 1) {p q : ι}
    (hp : p ∈ (longInteractionEndpointQubits P embedding threshold)ᶜ)
    (hpq : p ≠ q) :
    P.fixedGeneratorDecoupled
      ((daiLiSingletonSubsystem p).selected : Set ι)
      ((daiLiSingletonSubsystem q).selected : Set ι) := by sorry
