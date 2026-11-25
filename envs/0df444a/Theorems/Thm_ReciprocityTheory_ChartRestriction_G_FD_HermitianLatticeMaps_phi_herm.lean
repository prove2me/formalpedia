-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_herm
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.phi_herm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:05.361662+00:00
-- url     : https://prove2.me/theorems/3ffca54a-7a27-46aa-b5c1-f74de9577bfc
-- title:
--   Hermitian Lattice Maps: phi herm
-- statement:
--   The Hermitian Lattice Maps construction uses the phi herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianLatticeMaps.lean#L120-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianLatticeMaps.lean#L120-L137

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

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.phi_herm (h : ty X f = ty X f') (x y : Fin r → E) :
    herm X.Gm (phi X f f' x) (phi X f f' y) = herm X.Gm x y := by sorry
