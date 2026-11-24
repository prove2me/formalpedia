-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:54.331802+00:00
-- url     : https://prove2.me/theorems/4a213826-c750-4263-b79e-534767844fd5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux not mem ker iff aeval ne 69965e549228: P2 M Ground Theory Heights  Heights Inter Diag RAux not mem ker iff aeval ne 69965e549228
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux not mem ker iff aeval ne 69965e549228 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux not mem ker iff aeval ne 69965e549228 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L208-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L208-L216

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228 (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    s ∉ RingHom.ker (T.multiConeMap c) ↔ aeval c s ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«not_mem_ker_iff_aeval_ne» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_not_mem_ker_iff_aeval_ne_69965e549228
