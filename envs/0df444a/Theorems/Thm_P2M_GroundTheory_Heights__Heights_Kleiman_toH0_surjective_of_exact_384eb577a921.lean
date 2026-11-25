-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_toH0_surjective_of_exact_384eb577a921
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_toH0_surjective_of_exact_384eb577a921
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:44.26353+00:00
-- url     : https://prove2.me/theorems/b3ae0c4b-20ed-4749-a799-ce672d3a26d0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman to H0 surjective of exact 384eb577a921: P2 M Ground Theory Heights  Heights Kleiman to H0 surjective of exact 384eb577a921
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman to H0 surjective of exact 384eb577a921 construction uses the P2 M Ground Theory Heights  Heights Kleiman to H0 surjective of exact 384eb577a921 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L313-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L313-L328

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
universe u v w w'

theorem P2M_GroundTheory_Heights__Heights_Kleiman_toH0_surjective_of_exact_384eb577a921 (hC : CechExact.Statement.{u, w}) {S : Type u} [CommRing S]
    [IsNoetherianRing S] {N : ℕ} {K F M : Type w}
    [AddCommGroup K] [Module (Poly S N) K] [Module S K] [IsScalarTower S (Poly S N) K]
    [AddCommGroup F] [Module (Poly S N) F] [Module S F] [IsScalarTower S (Poly S N) F]
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    {𝓚 : GradedPMod S N K} {𝓕 : GradedPMod S N F} {𝓜 : GradedPMod S N M}
    (ι : GradedHom 𝓚 𝓕) (φ : GradedHom 𝓕 𝓜) (hι : Function.Injective ι.toLin)
    (hφ : Function.Surjective φ.toLin) (hex : Function.Exact ι.toLin φ.toLin) (c : ℤ)
    (hF : Function.Surjective (toH0 𝓕 c)) (hK : Subsingleton (cohom 𝓚 1 c)) :
    Function.Surjective (toH0 𝓜 c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«toH0_surjective_of_exact» := P2M_GroundTheory_Heights__Heights_Kleiman_toH0_surjective_of_exact_384eb577a921
