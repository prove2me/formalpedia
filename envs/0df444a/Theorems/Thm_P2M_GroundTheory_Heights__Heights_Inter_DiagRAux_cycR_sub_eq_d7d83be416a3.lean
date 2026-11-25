-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_sub_eq_d7d83be416a3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_sub_eq_d7d83be416a3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:25:31.270562+00:00
-- url     : https://prove2.me/theorems/22d1c818-6e91-4f2f-bf45-7e61ae11f535
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R sub eq d7d83be416a3: P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R sub eq d7d83be416a3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R sub eq d7d83be416a3 construction uses the P2 M Ground Theory Heights  Heights Inter Diag RAux cyc R sub eq d7d83be416a3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L158-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean#L158-L177

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_sub_eq_d7d83be416a3 (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (f g : MRing ι) (W₀ : Ideal (MRing ι))
    (hdiv : T.toZCycle (divCycle P f) - T.toZCycle (divCycle P g) = Finsupp.single W₀ 1)
    (hW₀ : IsHorizontal W₀) : cycR I P L f - cycR I P L g = I W₀ n L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagRAux».«cycR_sub_eq» := P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_sub_eq_d7d83be416a3
