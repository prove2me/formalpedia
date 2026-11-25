-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMap_X_inr_78c69b7b7f9a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMap_X_inr_78c69b7b7f9a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:33.98542+00:00
-- url     : https://prove2.me/theorems/321e187f-156c-4d41-bd82-8a14e72761f1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Map X inr 78c69b7b7f9a: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Map X inr 78c69b7b7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Map X inr 78c69b7b7f9a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter flag Map X inr 78c69b7b7f9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagArith.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagArith.lean#L42-L46

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMap_X_inr_78c69b7b7f9a (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    flagMap P B (X (⟨Sum.inr j, S⟩ : Σ k, FlagBundleBlocks ι N1 n k)) =
      flagMinor (genMat (FnField P) n * B.map C) j S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«flagMap_X_inr» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_flagMap_X_inr_78c69b7b7f9a
