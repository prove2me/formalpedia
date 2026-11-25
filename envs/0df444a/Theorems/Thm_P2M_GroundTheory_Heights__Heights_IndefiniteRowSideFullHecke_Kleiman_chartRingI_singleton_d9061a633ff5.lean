-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_chartRingI_singleton_d9061a633ff5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_chartRingI_singleton_d9061a633ff5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:55.091059+00:00
-- url     : https://prove2.me/theorems/46db6f69-9002-4ac7-875a-f91974b2c4ea
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman chart Ring I singleton d9061a633ff5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman chart Ring I
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman chart Ring I singleton d9061a633ff5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman chart Ring I singleton d9061a633ff5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L245-L250

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
open MvPolynomial
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo
variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_chartRingI_singleton_d9061a633ff5 (x : Fin (N + 1) → Ω) (i : Fin (N + 1)) :
    chartRingI S x {i} = chartRing S x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kleiman».«chartRingI_singleton» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_chartRingI_singleton_d9061a633ff5
