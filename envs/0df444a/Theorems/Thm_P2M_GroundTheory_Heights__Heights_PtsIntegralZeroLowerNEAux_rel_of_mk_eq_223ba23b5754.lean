-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_rel_of_mk_eq_223ba23b5754
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_rel_of_mk_eq_223ba23b5754
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:55.431028+00:00
-- url     : https://prove2.me/theorems/3f158e8c-32a5-479f-a9cb-474cd0486ccc
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux rel of mk eq 223ba23b5754: P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux rel of mk eq 223ba23b5754
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux rel of mk eq 223ba23b5754 construction uses the P2 M Ground Theory Heights  Heights Pts Integral Zero Lower NEAux rel of mk eq 223ba23b5754 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L18-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PPtsIntegralZeroLowerNE.lean#L18-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPtsIntegralZeroLowerNE
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.PtsIntegralZeroLowerNEAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_rel_of_mk_eq_223ba23b5754 {W : Ideal (MRing ι)} {a b : mcPts W}
    (h : (Quot.mk _ a : McClasses W) = Quot.mk _ b) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (b : (Σ k, ι k) → ℂ) = fun p => c p.1 * (a : (Σ k, ι k) → ℂ) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralZeroLowerNEAux».«rel_of_mk_eq» := P2M_GroundTheory_Heights__Heights_PtsIntegralZeroLowerNEAux_rel_of_mk_eq_223ba23b5754
