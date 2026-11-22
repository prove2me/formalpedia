-- Prove2me | Theorems.Thm_ShiSpread_sum_spread_reindex_of_injective
-- name    : ShiSpread.sum_spread_reindex_of_injective
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-11T09:43:10.373183+00:00
-- url     : https://prove2.me/theorems/b794e325-1c59-4c3e-aff3-b432467efab0
-- title:
--   Summing a zero-vanishing weight over a spread state reindexes to the small register
-- statement:
--   Let $e$ be an injective wire embedding, $\\chi$ an $m$-wire amplitude array, and $H:\\{0,1\\}^m\\times\\mathbb{C}\\to\\mathbb{R}$ any weight with $H(z,0)=0$. Then
--
--   $$\\sum_{y\\in\\{0,1\\}^n}H\\big(y|_e,\\ (\\mathrm{spread}_e\\chi)(y)\\big)=\\sum_{z\\in\\{0,1\\}^m}H(z,\\chi(z)).$$
--
--   Mechanism: $(\\mathrm{spread}_e\\chi)(y)=0$ unless $y$ vanishes on every wire off the image of $e$, so $H(\\cdot,0)=0$ kills the rest; and $y\\mapsto y|_e$ bijects the off-image-zero strings onto $\\{0,1\\}^m$, with inverse 'extend by $0$ off the image'.
--
--   **Why the weight carries the string argument.** Specialising $H(z,a)=F(a)$ gives the plain $\\sum_y F((\\mathrm{spread}_e\\chi)(y))=\\sum_z F(\\chi(z))$ for any $F$ with $F(0)=0$. The $z$-slot is kept because an output-wire condition on wire $e\\,\\mathrm{out}$ reads $y(e\\,\\mathrm{out})=y|_e(\\mathrm{out})$, which the $F$-only form cannot express — so the narrower version would not actually close the acceptance-probability step.
--
--   **Injectivity is essential, not a convenience.** For non-injective $e$, $\\mathrm{spread}_e$ drops the amplitudes of $\\chi$ at strings differing within a fibre of $e$ and the identity fails.
--
--   **Not proved.** No claim that $\\mathrm{spread}$ is linear, injective, isometric or norm-preserving; with $H(z,a)=\\lVert a\\rVert^2$ this gives norm preservation of the SUM only, and that specialisation is not recorded as a theorem. Nothing about $\\mathrm{acceptProb}$, $\\mathrm{outDist}$, measurement or mixed states, and nothing about $\\mathrm{restrict}$ as a map on amplitude arrays (no such pullback exists in the bundle). Proved for GENERAL injective $e$, not merely the canonical inclusion.

import Definitions.Def_ShiSpread_Core
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter

namespace ShiSpread

open ShiShallow in
/-- **Support reindexing for `spread` along an injective embedding.** If a weight `H` vanishes
on amplitude `0` for every small-register string, then summing `H (restrict e y) (spread e χ y)`
over all `n`-wire strings equals summing `H z (χ z)` over all `m`-wire strings: strings nonzero
off the image of `e` contribute nothing, and `restrict e` bijects the rest onto `Bits m`.

The first argument of `H` is the restricted string, which is what an output-wire condition needs
(`y (e out) = restrict e y out`). Taking `H` constant there gives the plain
`∑ y, F (spread e χ y) = ∑ z, F (χ z)` for `F 0 = 0`.

A statement about a SUM only: it does not assert `spread` is norm-preserving, nor anything about
`acceptProb`, and it is FALSE without injectivity. -/
theorem sum_spread_reindex_of_injective {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (χ : QState m) (H : Bits m → ℂ → ℝ)
    (hH : ∀ z : Bits m, H z 0 = 0) :
    ∑ y : Bits n, H (restrict e y) (spread e χ y) = ∑ z : Bits m, H z (χ z) := by sorry

end ShiSpread
