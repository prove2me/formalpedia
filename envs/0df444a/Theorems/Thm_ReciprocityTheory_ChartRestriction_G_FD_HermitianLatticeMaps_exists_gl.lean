-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_exists_gl
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.exists_gl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:13.303705+00:00
-- url     : https://prove2.me/theorems/4e034e02-a409-4457-b4a2-805b26863e9a
-- title:
--   Hermitian Lattice Maps: exists gl
-- statement:
--   The Hermitian Lattice Maps construction uses the exists gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianLatticeMaps.lean#L144-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianLatticeMaps.lean#L144-L175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
open Matrix NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (f f' : Basis ι ℤ X.Λ)
variable {f f'}

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.exists_gl (h : ty X f = ty X f') :
    ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by sorry
