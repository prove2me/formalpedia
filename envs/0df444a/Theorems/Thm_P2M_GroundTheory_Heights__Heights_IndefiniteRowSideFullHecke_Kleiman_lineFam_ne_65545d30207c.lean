-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_lineFam_ne_65545d30207c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_lineFam_ne_65545d30207c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:22.346129+00:00
-- url     : https://prove2.me/theorems/7633a8da-93e3-45c3-86ff-caa1bc946b4a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman line Fam ne 65545d30207c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman line Fam ne 65545d30207c
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman line Fam ne 65545d30207c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kleiman line Fam ne 65545d30207c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L685-L686
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CoordIdealIsMultiProjPrime.lean#L685-L686

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
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]
variable (S N)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_lineFam_ne_65545d30207c (k : Type) [Field k] : (1 : RatFunc k) ∈ (lineFam k).lat 0 ∧ (1 : RatFunc k) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kleiman».«lineFam_ne» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kleiman_lineFam_ne_65545d30207c
