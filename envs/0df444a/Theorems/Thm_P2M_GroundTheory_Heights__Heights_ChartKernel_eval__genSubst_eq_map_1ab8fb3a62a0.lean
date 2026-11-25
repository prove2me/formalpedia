-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0
-- name    : P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:21.973227+00:00
-- url     : https://prove2.me/theorems/e404043e-3fc4-4b43-9bc4-79379ffbc08b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Kernel eval  gen Subst eq map 1ab8fb3a62a0: P2 M Ground Theory Heights  Heights Chart Kernel eval  gen Subst eq map 1ab8fb3a62a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Kernel eval  gen Subst eq map 1ab8fb3a62a0 construction uses the P2 M Ground Theory Heights  Heights Chart Kernel eval  gen Subst eq map 1ab8fb3a62a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartKernel.lean#L122-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0 {B : Type*} [CommRing B] {e : ℕ} (q : MvPolynomial (Fin n) F →+* B)
    (t : Fin n → F) (g : MvPolynomial (Fin e × Fin n) F) :
    eval₂ (C.comp (q.comp C)) (genSubst (fun m => q (X m)) (fun m => q (C (t m)))) g =
      map q (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartKernel».«eval₂_genSubst_eq_map» := P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0
