-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_herm_symm
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:09.024687+00:00
-- url     : https://prove2.me/theorems/3a2ac318-e95f-4936-8f43-3a2619a205e5
-- title:
--   Hermitian Pairing Algebra: herm symm
-- statement:
--   The Hermitian Pairing Algebra construction uses the herm symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L45-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm {r : ℕ} {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by sorry
