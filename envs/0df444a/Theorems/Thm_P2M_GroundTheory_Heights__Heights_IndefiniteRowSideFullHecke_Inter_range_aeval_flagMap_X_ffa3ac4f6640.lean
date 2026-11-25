-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_range_aeval_flagMap_X_ffa3ac4f6640
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_range_aeval_flagMap_X_ffa3ac4f6640
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:07.788202+00:00
-- url     : https://prove2.me/theorems/504e5f36-19a0-4f57-9c81-d2f241a73545
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter range aeval flag Map X ffa3ac4f6640: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter range aeval flag
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter range aeval flag Map X ffa3ac4f6640 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter range aeval flag Map X ffa3ac4f6640 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagConeTrdeg.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagConeTrdeg.lean#L27-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagConeTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_range_aeval_flagMap_X_ffa3ac4f6640 (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range =
      Algebra.adjoin ℤ
        (Set.range (fun d : MRing ι ⧸ P => algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))
            (algebraMap (MRing ι ⧸ P) (FnField P) d)) ∪
          Set.range fun q : Σ j, PluckerBlocks N1 n j => flagMinor (genMat (FnField P) n * B.map C) q.1 q.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«range_aeval_flagMap_X» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_range_aeval_flagMap_X_ffa3ac4f6640
