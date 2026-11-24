-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_rename_56826dea6eef
-- name    : P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_rename_56826dea6eef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:41.109376+00:00
-- url     : https://prove2.me/theorems/9e6a7bc7-f76c-4dd4-9e95-bdaddbda60ca
-- title:
--   P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst rename 56826dea6eef: P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst rename 56826dea6eef
-- statement:
--   The P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst rename 56826dea6eef construction uses the P2 M Ground Theory Heights  Heights Isolated Fibre Open Poly graph Subst rename 56826dea6eef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIsolatedFibreOpenPoly.lean#L61-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
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
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_rename_56826dea6eef (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    graphSubst p (rename (Fin.castAdd d) q) = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsolatedFibreOpenPoly».«graphSubst_rename» := P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphSubst_rename_56826dea6eef
