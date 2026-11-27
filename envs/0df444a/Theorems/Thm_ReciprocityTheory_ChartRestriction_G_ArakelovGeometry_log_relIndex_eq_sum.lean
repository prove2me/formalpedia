-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_log_relIndex_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.log_relIndex_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:01.584239+00:00
-- url     : https://prove2.me/theorems/99e96e0b-df60-4476-bff6-ea92b4450766
-- title:
--   Arakelov Geometry: log rel Index eq sum
-- statement:
--   The Arakelov Geometry construction uses the log rel Index eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/RelIndexNeZeroOfMulMem.lean#L58-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/RelIndexNeZeroOfMulMem.lean#L58-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_RelIndexNeZeroOfMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
variable {κ : Type} [Fintype κ]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.log_relIndex_eq_sum (x x' : κ → Ω) (hle : sec ℤ x 1 ≤ sec ℤ x' 1)
    (hfin : ∃ M : ℕ, 0 < M ∧ ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) (n : ℕ) :
    Real.log ((sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x' n).toAddSubgroup) =
      ∑ j ∈ Finset.range n,
      Real.log ((sec ℤ x (n - j) * sec ℤ x' j).toAddSubgroup.relIndex
        (sec ℤ x (n - j - 1) * sec ℤ x' (j + 1)).toAddSubgroup) := by sorry
