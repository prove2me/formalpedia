-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_hermC_uvec
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.hermC_uvec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:04.233277+00:00
-- url     : https://prove2.me/theorems/65328a35-a709-56f0-95dd-b136d8eea9bb
-- title:
--   Lattice Minor Existence: herm C uvec
-- statement:
--   The Lattice Minor Existence construction uses the herm C uvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeMinorExistence.lean#L58-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeMinorExistence.lean#L58-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.hermC_uvec {u : Fin 2 → Fin r → E} (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (a b : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.uvec u a τ) (X.uvec u b τ) = 0 := by sorry
