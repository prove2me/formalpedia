-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_flagMap_X_2c846709d619
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_flagMap_X_2c846709d619
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:21.30405+00:00
-- url     : https://prove2.me/theorems/4e3816e9-96ef-5ec2-90ea-72e272d99ab2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval flag Map X 2c846709d619: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval flag Map X 2c8467
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval flag Map X 2c846709d619 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter aeval flag Map X 2c846709d619 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagConeTrdeg.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagConeTrdeg.lean#L18-L23

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_flagMap_X_2c846709d619 (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    ((aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
      MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) = flagMap P B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«aeval_flagMap_X» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_flagMap_X_2c846709d619
