-- Prove2me | Theorems.Thm_SecondBestTrade_HalfEfficiency_duality
-- name    : SecondBestTrade.HalfEfficiency.duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:11.795178+00:00
-- url     : https://prove2.me/theorems/425d6ae9-5282-49b4-a00c-3d1b97294f33
-- title:
--   Theorem 5.3 — Duality
-- statement:
--   For every useful dual $z=(\tau,\alpha,\beta)$, let $D(z)=(1+\tau)\mathbb E_\pi\widetilde H$. Then
--   $$\mathrm{SB}\le D(z),\qquad \mathrm{SB}=\min_{z\ \mathrm{useful}}D(z),$$
--   and the minimum is attained by a useful dual.
--
--   The lower envelope is over exactly the nonnegative useful-flow domain. An explicit minimizing witness accompanies the infimum equality; compactness is not assumed.
--
--   Differences from the source:
--   - encoding: finite agent, trade and support sets with product-prior expectations → Fin labels, an injective nonnegative-vector support embedding, and finite product-weighted sums; reason: bijections cover every finite source market, and summing an overwritten own coordinate multiplies by its total probability one
--   - encoding: attained minimum of useful dual objectives → real infimum equality together with a useful dual attaining SB and the universal lower bound; reason: the witness and the bound make this exactly the minimum assertion, including nonemptiness and boundedness
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Theorem 5.3 — Duality, printed p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Theorem 5.3, printed p. 9 (PDF p. 10). -/
theorem duality (N : Market) :
    (∀ z : Dual N, useful N z → SB N ≤ dualObjective N z) ∧
    SB N = sInf {r | ∃ z : Dual N, useful N z ∧ r = dualObjective N z} ∧
    ∃ z : Dual N, useful N z ∧ dualObjective N z = SB N := by sorry

end SecondBestTrade.HalfEfficiency
