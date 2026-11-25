-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeInclusion_toH0_ad3069c41239
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_freeInclusion_toH0_ad3069c41239
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:37:11.531107+00:00
-- url     : https://prove2.me/theorems/cf5d28f9-c57d-531b-836d-55c98d83a85e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman free Inclusion to H0 ad3069c41239: P2 M Ground Theory Heights  Heights Kleiman free Inclusion to H0 ad3069c41239
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman free Inclusion to H0 ad3069c41239 construction uses the P2 M Ground Theory Heights  Heights Kleiman free Inclusion to H0 ad3069c41239 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L200-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean#L200-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
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
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb

theorem P2M_GroundTheory_Heights__Heights_Kleiman_freeInclusion_toH0_ad3069c41239 (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    freeIncl 𝓜 b d hb 0 c j (toH0 (polyGraded S N) (c - d j) p) =
      toH0 𝓜 c ⟨(p : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j p⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«freeInclusion_toH0» := P2M_GroundTheory_Heights__Heights_Kleiman_freeInclusion_toH0_ad3069c41239
