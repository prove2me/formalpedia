-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e
-- name    : P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:35.369471+00:00
-- url     : https://prove2.me/theorems/1be59049-7afc-4090-bf27-645a5d13cd10
-- title:
--   P2 M Global Theory Pull Hermitian val At  eq unit Val 3711952a0e7e: P2 M Global Theory Pull Hermitian val At  eq unit Val 3711952a0e7e
-- statement:
--   The P2 M Global Theory Pull Hermitian val At  eq unit Val 3711952a0e7e construction uses the P2 M Global Theory Pull Hermitian val At  eq unit Val 3711952a0e7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L19-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val = unitVal x h f := by sorry

alias «GlobalTheory».«PullHermitian».«valAt'_eq_unitVal» := P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e
