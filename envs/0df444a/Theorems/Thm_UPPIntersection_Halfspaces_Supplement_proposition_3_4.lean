-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_proposition_3_4
-- name    : UPPIntersection.Halfspaces.Supplement.proposition_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:59:50.621734+00:00
-- url     : https://prove2.me/theorems/feda4d15-96ef-4257-ad45-854c16cdc51d
-- title:
--   Proposition 3.4 — parity, spherical averaging, boundedness, dimension reduction and derivative recurrence of $G^d_i$
-- statement:
--   Let $d\ge2$ and let $G^d_0,G^d_1,\dots$ be the normalized Gegenbauer polynomials (Definition 3.3). Write $\sigma_d$ for the uniform probability measure on $S^{d-1}$.
--
--   1. **(Anti-)symmetry.** For every $i$ and $t\in[-1,1]$, $G^d_i(-t)=(-1)^iG^d_i(t)$.
--   2. **Spherical averaging.** Let $q:S^{d-1}\to\mathbb R$ be a polynomial of degree at most $i$ with $\mathbb E_{Y\sim\sigma_d}[q(Y)r(Y)]=0$ for every polynomial $r$ of degree less than $i$. Then for every $x\in S^{d-1}$ and $t\in[-1,1]$,
--   $$P_x(t):=\mathop{\mathbb E}_{U\in S^{d-1}:\langle U,x\rangle=0}\Big[q\big(tx+\sqrt{1-t^2}\,U\big)\Big]=q(x)\,G^d_i(t),$$
--   where $U$ is uniform on the great subsphere orthogonal to $x$.
--   3. **Boundedness.** For every $i\ge0$ and $t\in[-1,1]$, $|G^d_i(t)|\le1$.
--   4. **Dimension reduction.** If $d\ge4$, then for every $i$ the polynomial $G^d_i$ is a convex combination of the polynomials $G^{d-2}_j$ with $0\le j\le i$ and $j\equiv i\pmod 2$.
--   5. **Derivative recurrence.** If $d\ge4$, then for every $i\ge0$ and every real $t$,
--   $$(1-t^2)\frac{d}{dt}G^d_i(t)=(d-3)\big(tG^d_i(t)-G^{d-2}_{i+1}(t)\big).$$
--
--   These facts are the toolkit of §3.1: boundedness, dimension reduction and the derivative recurrence drive the derivative bound of Theorem 3.5, and spherical averaging gives the correlation formula of Lemma 3.6.
--
--   **Formalization Note** Clause 4 is an identity of polynomials with nonnegative weights summing to one over the indices of the right parity; clause 5 is likewise an identity of polynomials, hence holds at every real $t$.
--
--   Differences from the source:
--   - encoding: G^d_i defined as the unique degree-i polynomials orthogonal for v_d(t)=(1−t²)^((d−3)/2) on [−1,1] with G^d_i(1)=1 (Definition 3.3) → the published SphereSOS.Rate.geg, defined by G_0=1, G_1=t and (k+d−1)G_{k+2}=(2k+d)tG_{k+1}−(k+1)G_k; reason: this recurrence defines the same normalized Gegenbauer polynomials for every d ≥ 2 (Chebyshev polynomials at d=2); the identification is a fact to be used, not an assumption
--   - generalization: q a degree-i polynomial on S^{d−1} → q a polynomial of degree at most i on S^{d−1}; reason: a polynomial of degree < i that is orthogonal to all polynomials of degree < i is orthogonal to itself, hence zero, and both sides vanish; the source's case is included
--   - encoding: orthogonal to every polynomial r of degree at most (i − 1) → orthogonal to every polynomial r of degree n for some n < i; reason: same condition; avoids natural-number subtraction at i = 0
--   - encoding: U uniform on the great subsphere {U ∈ S^{d−1} : ⟨U,x⟩=0} → U is the normalized projection of an independent uniform point of S^{d−1} onto x^⊥, as in the published partner/symH experiment D_s; reason: this is the uniform law on the great subsphere; the projection is undefined only on a null set
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 16, Proposition 3.4 (items 1–5); proofs in Appendix A.2, pp. 37–39; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_SphereSOS_Rate_Gegenbauer
import Definitions.Def_UPPIntersection_Halfspaces_Supplement_Defs

open MeasureTheory SphereSOS.Rate

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Proposition 3.4 (p. 16; proofs in Appendix A.2, pp. 37–39). The normalized
Gegenbauer polynomials `G^d_i = geg d i` satisfy, for every `d ≥ 2`: (1) parity, (2) the spherical
averaging identity, (3) boundedness on `[-1,1]`, (4) dimension reduction for `d ≥ 4`, and (5) the
derivative recurrence for `d ≥ 4`. In (2) the expectation over `U` uniform on the great subsphere
`{U : ⟨U,x⟩ = 0}` is the published `partner` experiment `t x + √(1-t²) U`. -/
theorem proposition_3_4 (d : ℕ) (hd : 2 ≤ d) :
    (∀ i : ℕ, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      (geg d i).eval (-t) = (-1) ^ i * (geg d i).eval t) ∧
    (∀ (i : ℕ) (q : Sph d → ℝ), IsSphPolyLE d i q →
      (∀ (n : ℕ) (r : Sph d → ℝ), n < i → IsSphPolyLE d n r →
        ∫ y, q y * r y ∂(sphereLaw d) = 0) →
      ∀ (x : Sph d), ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        ∫ u, q (partner t x u) ∂(sphereLaw d) = q x * (geg d i).eval t) ∧
    (∀ i : ℕ, ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(geg d i).eval t| ≤ 1) ∧
    (4 ≤ d → ∀ i : ℕ, ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧
      ∑ j ∈ (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2), c j = 1 ∧
      geg d i = ∑ j ∈ (Finset.range (i + 1)).filter (fun j => j % 2 = i % 2),
        Polynomial.C (c j) * geg (d - 2) j) ∧
    (4 ≤ d → ∀ (i : ℕ) (t : ℝ),
      (1 - t ^ 2) * (Polynomial.derivative (geg d i)).eval t =
        ((d : ℝ) - 3) * (t * (geg d i).eval t - (geg (d - 2) (i + 1)).eval t)) := by sorry

end UPPIntersection.Halfspaces.Supplement
