-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPsiBounds_herm_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.herm_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:30:19.187741+00:00
-- url     : https://prove2.me/theorems/73b8aa26-b86a-4c72-935d-35e5f72f664a
-- title:
--   Hermitian Psi Bounds: herm bound
-- statement:
--   The Hermitian Psi Bounds construction uses the herm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPsiBounds.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianPsiBounds.lean#L95-L108

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

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.herm_bound {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IntegralBasisReduction.IsNormal X y) (σ : E →+* ℂ)
    (p q : Fin r → E) : ‖σ (herm X.Gm p q)‖ ≤ (Qy X y p + Qy X y q) * Cinv X := by sorry
