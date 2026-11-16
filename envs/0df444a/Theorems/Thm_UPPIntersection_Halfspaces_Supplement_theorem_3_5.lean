-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_3_5
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:20.44263+00:00
-- url     : https://prove2.me/theorems/779da7d1-b222-4c60-809b-b99760ef2357
-- title:
--   Theorem 3.5 — derivative bound $|(G^d_i)^{(D)}(t)|/D!\le(3/(1-\rho))^D$ on $[-\rho,\rho]$
-- statement:
--   Let $\rho\in[0,1)$. For every order of differentiation $D\ge0$, every dimension $d\ge2D+2$ and every degree $i\ge0$, the normalized Gegenbauer polynomial $G^d_i$ satisfies
--   $$\max_{t\in[-\rho,\rho]}\frac{|(G^d_i)^{(D)}(t)|}{D!}\le\Big(\frac{3}{1-\rho}\Big)^D.$$
--
--   The bound is uniform in the degree $i$; only the dimension must grow with the derivative order. Together with the absolute summability of Theorem 3.7 it gives the derivative bounds of Theorem 3.1 for the spherical symmetrization $H_{f,g}$.
--
--   **Formalization Note** The maximum is stated as a bound at every point of $[-\rho,\rho]$, which is equivalent because a polynomial is continuous and the interval is compact and nonempty; $(G^d_i)^{(D)}$ is the $D$-fold formal derivative.
--
--   Differences from the source:
--   - encoding: G^d_i defined as the unique degree-i polynomials orthogonal for v_d(t)=(1−t²)^((d−3)/2) on [−1,1] with G^d_i(1)=1 (Definition 3.3) → the published SphereSOS.Rate.geg, defined by G_0=1, G_1=t and (k+d−1)G_{k+2}=(2k+d)tG_{k+1}−(k+1)G_k; reason: this recurrence defines the same normalized Gegenbauer polynomials for every d ≥ 2 (Chebyshev polynomials at d=2); the identification is a fact to be used, not an assumption
--   - encoding: max over t ∈ [−ρ,ρ] of |(G^d_i)^{(D)}(t)|/D! → the bound at every t ∈ [−ρ,ρ]; reason: the maximum of a continuous function on a nonempty compact interval is attained, so the two statements are equivalent
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 17, Theorem 3.5 (proof on p. 17); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

open SphereSOS.Rate

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 3.5 (p. 17). For `ρ ∈ [0,1)`, every derivative order `D ≥ 0`, every
dimension `d ≥ 2D + 2` and every degree `i ≥ 0`, the `D`-th derivative of the normalized Gegenbauer
polynomial `G^d_i` satisfies `|(G^d_i)^{(D)}(t)| / D! ≤ (3/(1-ρ))^D` at every `t ∈ [-ρ, ρ]`
(equivalently, the maximum over this compact interval is at most that bound). -/
theorem theorem_3_5 (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (D d i : ℕ) (hd : 2 * D + 2 ≤ d) :
    ∀ t ∈ Set.Icc (-ρ) ρ,
      |(Polynomial.derivative^[D] (geg d i)).eval t| / (D.factorial : ℝ) ≤ (3 / (1 - ρ)) ^ D := by sorry

end UPPIntersection.Halfspaces.Supplement
