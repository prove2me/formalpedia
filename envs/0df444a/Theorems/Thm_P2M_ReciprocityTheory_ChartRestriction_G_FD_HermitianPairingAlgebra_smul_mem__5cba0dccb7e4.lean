-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_smul_mem__5cba0dccb7e4
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_smul_mem__5cba0dccb7e4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:16.799169+00:00
-- url     : https://prove2.me/theorems/68b2ab5d-7ed6-4aa2-88bf-3673fda07a7a
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Hermitian Pairing Algebra smul mem  5cba0dccb7e4: P2 M Reciprocity Theory Chart Restriction G FD Hermitian Pairing Algebra smul mem  5cba0dccb7e4
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Hermitian Pairing Algebra smul mem  5cba0dccb7e4 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Hermitian Pairing Algebra smul mem  5cba0dccb7e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPairingAlgebra.lean#L51-L55

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_smul_mem__5cba0dccb7e4 {r : ℕ} {M : Submodule (𝓞 E) (Fin r → E)} {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ M) : a • y ∈ M := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«HermitianPairingAlgebra».«smul_mem'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_smul_mem__5cba0dccb7e4
