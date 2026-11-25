-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_genMap_basis_f97c744f41c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_genMap_basis_f97c744f41c8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:45.161059+00:00
-- url     : https://prove2.me/theorems/51b1a933-f5c7-5582-84a8-0cbc7f08b4ec
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graded Pres gen Map basis f97c744f41c8: P2 M Ground Theory Heights  Heights Kleiman Graded Pres gen Map basis f97c744f41c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graded Pres gen Map basis f97c744f41c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graded Pres gen Map basis f97c744f41c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L164-L169

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsPres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGradedPres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.GradedPres
variable {S : Type u} [CommRing S] {N : ℕ}
variable {r : ℕ}
variable {M : Type w} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_genMap_basis_f97c744f41c8 (𝓜 : GradedPMod S N M) (d : Fin r → ℤ) (m : Fin r → M)
    (hm : ∀ j, m j ∈ 𝓜.piece (d j)) (j : Fin r) :
    (genMap.{u, v} 𝓜 d m hm).toLin (freeBasis.{u, v} S N r j) = m j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GradedPres».«genMap_basis» := P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_genMap_basis_f97c744f41c8
