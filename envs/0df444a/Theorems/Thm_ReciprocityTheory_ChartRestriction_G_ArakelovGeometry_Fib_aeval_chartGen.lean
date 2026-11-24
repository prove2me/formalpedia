-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_aeval_chartGen
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_chartGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:58.027304+00:00
-- url     : https://prove2.me/theorems/4ba22012-4d68-40e5-93a9-e3ca19f291d6
-- title:
--   Fib: aeval chart Gen
-- statement:
--   The Fib construction uses the aeval chart Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStD.lean#L46-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.aeval_chartGen (y : Fin (D + 1) → Ω) (g : MvPolynomial {k : Fin (D + 1) // k ≠ 0} ℤ) :
    ((MvPolynomial.aeval (chartGen y) g : fnField y) : Ω) =
      deh y 0 (MvPolynomial.rename Subtype.val g) := by sorry
