-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_herm_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:20.243422+00:00
-- url     : https://prove2.me/theorems/363823cf-1252-4af5-b31f-1270fe9eef86
-- title:
--   Hermitian Pairing Algebra: herm smul right
-- statement:
--   The Hermitian Pairing Algebra construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L40-L43

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

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_smul_right {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G x (a • y) = cc a * herm G x y := by sorry
