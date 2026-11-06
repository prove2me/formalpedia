-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_product_decay
-- name    : RH.Transport.SupportedMass.product_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:46.330405+00:00
-- url     : https://prove2.me/theorems/a3a454dd-d10a-4be3-a1e4-9f644ff6cb05
-- title:
--   Supported Mass: product decay
-- statement:
--   The Supported Mass construction uses the product decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L124-L136
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L124-L136

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.product_decay {ι : Type*} (J : Finset ι)
    (mass C ell : ι → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hmass : ∀ i ∈ J, 0 ≤ mass i)
    (hbound : ∀ i ∈ J, mass i ≤ C i * Z ^ (-ell i / 2)) :
    (∏ i ∈ J, mass i) ≤
      (∏ i ∈ J, C i) * Z ^ (-(∑ i ∈ J, ell i) / 2) := by sorry
