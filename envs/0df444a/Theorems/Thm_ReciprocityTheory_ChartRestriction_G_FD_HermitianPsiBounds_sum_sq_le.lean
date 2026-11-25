-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPsiBounds_sum_sq_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.sum_sq_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:30:50.590702+00:00
-- url     : https://prove2.me/theorems/d7d552f4-cf8a-4384-b4f0-2b9d83ad7ded
-- title:
--   Hermitian Psi Bounds: sum sq le
-- statement:
--   The Hermitian Psi Bounds construction uses the sum sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPsiBounds.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPsiBounds.lean#L23-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.sum_sq_le (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) :
    ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 ≤ Qy X y p * Cinv X := by sorry
