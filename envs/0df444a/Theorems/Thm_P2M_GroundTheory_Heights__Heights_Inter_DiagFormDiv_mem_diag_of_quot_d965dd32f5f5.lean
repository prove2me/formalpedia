-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagFormDiv_mem_diag_of_quot_d965dd32f5f5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagFormDiv_mem_diag_of_quot_d965dd32f5f5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:05.804258+00:00
-- url     : https://prove2.me/theorems/e5879b86-e271-431d-9039-442847955633
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag Form Div mem diag of quot d965dd32f5f5: P2 M Ground Theory Heights  Heights Inter Diag Form Div mem diag of quot d965dd32f5f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag Form Div mem diag of quot d965dd32f5f5 construction uses the P2 M Ground Theory Heights  Heights Inter Diag Form Div mem diag of quot d965dd32f5f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagFormDiv.lean#L30-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsDiagFormDiv.lean#L30-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagFormDiv_mem_diag_of_quot_d965dd32f5f5 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) {n : ℕ} {g h : MRing (T.wwIdx ι ν κ)}
    (hg : IsMultiHomog g (T.wwDeg n 1)) (hh : IsMultiHomog h (T.wwDeg (n + 3) 0))
    (hq : aeval (T.wwCoord x δ e φ (a 0) (a 1)) g = T.diagSec a * aeval (T.wwCoord x δ e φ (a 0) (a 1)) h) :
    g ∈ T.wwIdeal x δ e φ (a 0) (a 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagFormDiv».«mem_diag_of_quot» := P2M_GroundTheory_Heights__Heights_Inter_DiagFormDiv_mem_diag_of_quot_d965dd32f5f5
