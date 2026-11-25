-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_exists_unitary_basis_same_flag
-- name    : ReciprocityTheory.ChartRestriction.G.FD.exists_unitary_basis_same_flag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:24:03.077606+00:00
-- url     : https://prove2.me/theorems/73aa58d9-2d8d-529b-883c-d8a81e24323e
-- title:
--   FD: exists unitary basis same flag
-- statement:
--   The FD construction uses the exists unitary basis same flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExistsUnitaryBasisSameFlag.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExistsUnitaryBasisSameFlag.lean#L31-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UbasisAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.exists_unitary_basis_same_flag (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r) (hξ : X.IsIso ξ)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0) (hflag : X.SameFlag z0 x0) :
    ∃ f : X.Ψ → Fin (r - 2) → Fin r → ℂ, X.UBasis z0 ξ f := by sorry
