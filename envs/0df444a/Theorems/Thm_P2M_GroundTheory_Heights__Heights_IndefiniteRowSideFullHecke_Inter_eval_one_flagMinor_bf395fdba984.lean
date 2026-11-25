-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_one_flagMinor_bf395fdba984
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_one_flagMinor_bf395fdba984
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:37.592773+00:00
-- url     : https://prove2.me/theorems/52a17b1e-0e21-5311-a3ab-2b2c0cef5ef0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval one flag Minor bf395fdba984: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval one flag Minor
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval one flag Minor bf395fdba984 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter eval one flag Minor bf395fdba984 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagArith.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagArith.lean#L48-L57

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_one_flagMinor_bf395fdba984 (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    eval (fun q : Fin n × Fin n => if q.1 = q.2 then (1 : FnField P) else 0)
      (flagMinor (genMat (FnField P) n * B.map C) j S) = flagMinor B j S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«eval_one_flagMinor» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_eval_one_flagMinor_bf395fdba984
