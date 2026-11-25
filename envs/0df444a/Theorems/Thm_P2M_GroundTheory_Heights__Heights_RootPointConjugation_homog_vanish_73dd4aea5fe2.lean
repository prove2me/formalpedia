-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_homog_vanish_73dd4aea5fe2
-- name    : P2M_GroundTheory_Heights__Heights_RootPointConjugation_homog_vanish_73dd4aea5fe2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:42.646904+00:00
-- url     : https://prove2.me/theorems/43d27824-5900-5459-8744-0a1eebf2a8fa
-- title:
--   P2 M Ground Theory Heights  Heights Root Point Conjugation homog vanish 73dd4aea5fe2: P2 M Ground Theory Heights  Heights Root Point Conjugation homog vanish 73dd4aea5fe2
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Point Conjugation homog vanish 73dd4aea5fe2 construction uses the P2 M Ground Theory Heights  Heights Root Point Conjugation homog vanish 73dd4aea5fe2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L26-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L26-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
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
open GroundTheory.Heights₂.Heights.RootPointConjugation

theorem P2M_GroundTheory_Heights__Heights_RootPointConjugation_homog_vanish_73dd4aea5fe2 {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (z : (Σ _ : Fin f, PlIdx j m) → ℂ) (hz : z ∈ mcPts (rootPointIdeal ζ)) (τ : Fin f)
    (u : PlIdx j m → ℂ) (hu : ∀ I, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * u I)
    (Q : MvPolynomial (PlIdx j m) ℤ) (hQ : aeval (fun I => rootCoord ζ ⟨τ, I⟩) Q = 0) :
    z ⟨τ, plAnchor j m⟩ ^ Q.totalDegree * aeval u Q = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointConjugation».«homog_vanish» := P2M_GroundTheory_Heights__Heights_RootPointConjugation_homog_vanish_73dd4aea5fe2
