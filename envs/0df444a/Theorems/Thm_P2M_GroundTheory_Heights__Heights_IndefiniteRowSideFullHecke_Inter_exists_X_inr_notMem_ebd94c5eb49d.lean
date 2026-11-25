-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_X_inr_notMem_ebd94c5eb49d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_X_inr_notMem_ebd94c5eb49d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:56.102131+00:00
-- url     : https://prove2.me/theorems/748f762c-d3ce-56e4-90c5-02e2d9fdf91b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists X inr not Mem ebd94c5eb49d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists X inr not Me
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists X inr not Mem ebd94c5eb49d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists X inr not Mem ebd94c5eb49d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagArith.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagArith.lean#L59-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagBundleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
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
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_X_inr_notMem_ebd94c5eb49d (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B)
    (j : Fin (n - 1)) : ∃ S : PluckerBlocks N1 n j, (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) ∉ flagIdeal P B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«exists_X_inr_notMem» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_X_inr_notMem_ebd94c5eb49d
