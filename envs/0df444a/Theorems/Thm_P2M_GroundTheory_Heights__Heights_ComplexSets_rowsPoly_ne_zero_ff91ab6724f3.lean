-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_rowsPoly_ne_zero_ff91ab6724f3
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_rowsPoly_ne_zero_ff91ab6724f3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:12.354363+00:00
-- url     : https://prove2.me/theorems/79f5032c-21c2-51c1-9f38-bd13dae57b6b
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets rows Poly ne zero ff91ab6724f3: P2 M Ground Theory Heights  Heights Complex Sets rows Poly ne zero ff91ab6724f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets rows Poly ne zero ff91ab6724f3 construction uses the P2 M Ground Theory Heights  Heights Complex Sets rows Poly ne zero ff91ab6724f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericProjectionFinite.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericProjectionFinite.lean#L36-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_rowsPoly_ne_zero_ff91ab6724f3 {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«rowsPoly_ne_zero» := P2M_GroundTheory_Heights__Heights_ComplexSets_rowsPoly_ne_zero_ff91ab6724f3
