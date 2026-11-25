-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_exists_homogeneous_generators_86a8a5977c01
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_exists_homogeneous_generators_86a8a5977c01
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:13.280487+00:00
-- url     : https://prove2.me/theorems/0dd8357f-db3f-5d67-8dfb-a8825f5af665
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Graded Pres exists homogeneous generators 86a8a5977c01: P2 M Ground Theory Heights  Heights Kleiman Graded Pres exists homogeneous generators 86a8a5977c01
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Graded Pres exists homogeneous generators 86a8a5977c01 construction uses the P2 M Ground Theory Heights  Heights Kleiman Graded Pres exists homogeneous generators 86a8a5977c01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L235-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGradedPres.lean#L235-L264

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_exists_homogeneous_generators_86a8a5977c01 {S : Type u} [CommRing S] {N : ℕ} {M : Type w}
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M) (hfin : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (m : Fin r → M) (d : Fin r → ℤ), (∀ j, m j ∈ 𝓜.piece (d j)) ∧
      Submodule.span (Poly S N) (Set.range m) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«GradedPres».«exists_homogeneous_generators» := P2M_GroundTheory_Heights__Heights_Kleiman_GradedPres_exists_homogeneous_generators_86a8a5977c01
