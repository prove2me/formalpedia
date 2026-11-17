-- Prove2me | Theorems.Thm_PolyTimeFactorization_hasse_bound
-- name    : PolyTimeFactorization.hasse_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T16:13:22.252242+00:00
-- url     : https://prove2.me/theorems/fc377003-b26e-4f80-b8d8-f7198be84783
-- title:
--   Hasse's bound on $\#E(\mathbb{F}_p)$ (foundation of ECM)
-- statement:
--   Hasse's theorem (the Hasse bound). Let $p$ be prime and let $W$ be a Weierstrass curve
--   $$Y^2+a_1XY+a_3Y=X^3+a_2X^2+a_4X+a_6$$
--   over $\mathbb{F}_p$ with nonzero discriminant $\Delta$ (equivalently, nonsingular, hence an elliptic curve). Let $N$ be the number of $\mathbb{F}_p$-rational points of the curve: the number of affine solutions $(x,y)\in\mathbb{F}_p^2$ of the Weierstrass equation, plus the single point at infinity. Then
--   $$|N-(p+1)|\le 2\sqrt{p}.$$
--
--   This bound is the theoretical foundation of Lenstra's elliptic curve method: it places the group order $\#E(\mathbb{F}_p)$ in the interval $[p+1-2\sqrt{p},\,p+1+2\sqrt{p}]$, which is what makes ECM's smoothness heuristic plausible. It is a deep theorem — equivalent to the Riemann hypothesis for the curve's function field — and is not yet formalized in Mathlib.
--
--   **Formalization Note.** The curve is Mathlib's `WeierstrassCurve (ZMod p)`; the affine solution set is counted with `Nat.card` over the subtype satisfying `WeierstrassCurve.Affine.Equation`, and the point at infinity contributes the explicit $+1$.
-- source:
--   H. Hasse (1933-1936); standard reference: J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., Springer GTM 106 (2009), Theorem V.1.1, https://doi.org/10.1007/978-1-4757-1920-8 ; ECM application: H. W. Lenstra Jr., Factoring integers with elliptic curves, Ann. of Math. 126 (1987), 649-673, https://doi.org/10.2307/1971363

import Mathlib

namespace PolyTimeFactorization

theorem hasse_bound (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) (hW : W.Δ ≠ 0) :
    |((Nat.card {xy : ZMod p × ZMod p // WeierstrassCurve.Affine.Equation W xy.1 xy.2} : ℝ) + 1)
        - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by sorry

end PolyTimeFactorization
