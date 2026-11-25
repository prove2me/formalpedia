-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_map_cone_faca59ddb66f
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_map_cone_faca59ddb66f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:33.283255+00:00
-- url     : https://prove2.me/theorems/4dd04ff5-ca62-40d9-afa6-ebc067bfad58
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Root Bound map cone faca59ddb66f: P2 M Ground Theory Heights  Heights Grassmannian Root Bound map cone faca59ddb66f
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Root Bound map cone faca59ddb66f construction uses the P2 M Ground Theory Heights  Heights Grassmannian Root Bound map cone faca59ddb66f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassLeRoot.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassLeRoot.lean#L20-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianRootBound
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_map_cone_faca59ddb66f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (y : (Σ k, ι k) → R)
    (g : MRing ι) : MvPolynomial.map φ (cone y g) = cone (fun p => φ (y p)) g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianRootBound».«map_cone» := P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_map_cone_faca59ddb66f
