-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_fibre_anchor_wp_spectrum_bound
-- name    : WeierstrassEllipticZeta.fibre_anchor_wp_spectrum_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T00:50:39.55253+00:00
-- url     : https://prove2.me/theorems/79bee622-e0c3-4e94-a398-f64b1e863ee6
-- title:
--   Whole-fibre anchors have at most 4n distinct regular elliptic values
-- statement:
--   Let L be a period pair, D normalized sigma differential data, and S the associated entire, nowhere-simultaneously-zero projective coordinates. Let Q be bihomogeneous of bidegree (m,n), with n>=1, and suppose its entire diagonal pullback is not identically zero.
--
--   There exists a nonzero univariate complex polynomial H of degree at most 4n whose distinct root set has cardinality at most 4n, such that every whole-fibre anchor b outside L's period lattice satisfies wp(b) in roots(H).
--
--   Here a whole-fibre anchor is exactly an anchor passing the existing finite fibre tests. Thus all regular whole-fibre anchors, even without restriction to a compact region, have at most 4n distinct elliptic values. The bound is independent of m, the vanishing order, and the finite set used in the zero estimate.
--
--   This does not bound the number of coordinates b, since multiple coordinates may have the same wp-value. Lattice anchors are excluded from this affine assertion. The root set can contain values which are not anchors, and no effective root-finding or anchor-enumeration algorithm is claimed.
--
--   The previous result proved qualitative finiteness of the anchor coordinates in a compact period region. This theorem adds a degree-based bound on their regular elliptic-value projection. It does not prove the global multiplicity upper bound.
-- source:
--   Derived algebraic fibre bound for Senthil Kumar K (2026), Appendix A.2, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The degree-4n bound is derived here, not quoted from the paper. Fix a nonzero regular slice, retain the Weierstrass cubic, and reduce to A(x)+y*B(x), with deg A<=2n and deg B<=2n-2. The norm A(x)^2-(4*x^3-g2*x-g3)*B(x)^2 is nonzero by degree parity and has degree at most 4n. Every whole-fibre anchor off the lattice projects to a root. This replaces qualitative compact-region finiteness by a uniform bound on distinct wp-values, not on the coordinates b themselves. The global geometric cost estimate is still required, now with this annihilator certificate available; the reduction preserves C exactly.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Polynomial.Roots
open WeierstrassEllipticZeta MvPolynomial

theorem WeierstrassEllipticZeta.fibre_anchor_wp_spectrum_bound
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hn : 1 ≤ n)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0) :
    ∃ H : Polynomial ℂ, H ≠ 0 ∧ H.natDegree ≤ 4 * n ∧
      H.roots.toFinset.card ≤ 4 * n ∧
      ∀ b : ℂ, b ∉ L.lattice → () ∈ fibreAnchorChoices S Q m n b →
        L.weierstrassP b ∈ H.roots.toFinset := by sorry
