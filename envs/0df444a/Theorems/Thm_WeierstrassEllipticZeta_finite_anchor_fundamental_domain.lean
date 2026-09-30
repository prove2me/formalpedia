-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_finite_anchor_fundamental_domain
-- name    : WeierstrassEllipticZeta.finite_anchor_fundamental_domain
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T15:03:04.400191+00:00
-- url     : https://prove2.me/theorems/802f2c87-5a28-40ce-98ab-073e979f68a1
-- title:
--   Compact period normalization of finite anchor candidates
-- statement:
--   Let L be a period pair, D its elliptic sigma differential data, and S the five everywhere analytic regularized projective coordinates. Assume that S agrees away from the period lattice with sigma cubed times (1, wp, wp', zeta, wp' zeta + 2 wp squared), that these coordinates never vanish simultaneously, and that eta is the actual quasiperiod map. Let X be any finite subset of C and Q any bihomogeneous polynomial of bidegree (m,n).
--
--   The closed period parallelogram spanned by the real basis (omega_1,omega_2) is compact. For every predicate P on the finite set of point, fibre and period-pair line candidates, the following conditions are equivalent:
--
--   - There exist b in C and a finite anchor candidate at b whose underlying locus candidate satisfies P.
--   - Such b and a exist with b in the closed period parallelogram and with norm(b) at most norm(omega_1)+norm(omega_2).
--
--   Finite anchor candidates are those in the existing FiniteAnchorCandidates definition: the origin point, the whole fibre when its finite tests pass, and period-pair lines with intercepts among the tested roots of the first nonzero slice polynomial. The construction preserves the exact underlying finite locus candidate. Consequently it preserves any condition depending on its shape or period kernel, including its degree parameter and quotient class count. Empty X and zero bidegrees are allowed.
--
--   This is a coordinate normalization derived from projective period descent. It does not assert that a candidate with a desired cost exists. The bounded coordinate still ranges over a continuum; no finite global search or improved integer-search bound is claimed.
-- source:
--   Derived compact period normalization for the A.1 frontier https://prove2.me/theorems/5c0ca929-d071-43e0-996d-dfa3194114a0. Primary analytic source: the period/quasiperiod law and exponential map at the beginning of Appendix A in Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. The Proved projective descent theorem ec2a2e1c-5f8f-4ae2-bb23-b71a175888c7 gives invariance of bihomogeneous vanishing under (b,u) -> (b-omega,u+eta(omega)), including lattice points. Canonical finite tests and line-root membership are preserved by this transport. Primary lattice reference: pinned Mathlib ZSpan.fract_mem_fundamentalDomain, ZSpan.fundamentalDomain_subset_parallelepiped and ZSpan.norm_fract_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Module/ZLattice/Basic.lean. Set omega=floor(b); the new b lies in the closed compact period parallelogram and has norm at most norm(omega_1)+norm(omega_2). The finite-anchor theorem and exact frontier equivalence are derived here, not quoted as the paper's zero estimate. The exact locus candidate, class count, degree parameter, chart cost and C are preserved. The coordinate b still ranges over a continuum; the global uniform cost estimate remains Open and the integer-search bound is unchanged.

import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential

noncomputable section
open scoped Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.finite_anchor_fundamental_domain
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (X : Finset ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    IsCompact (L.basis.parallelepiped : Set ℂ) ∧
      ∀ P : FiniteLocusCandidate L.lattice X → Prop,
        (∃ (b : ℂ) (a : FiniteAnchorCandidate L.lattice η X S Q m n b),
          P (anchorCandidateLocus L.lattice η X S Q m n b a)) ↔
        (∃ b : ℂ, b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ ∧
          ∃ a : FiniteAnchorCandidate L.lattice η X S Q m n b,
            P (anchorCandidateLocus L.lattice η X S Q m n b a)) := by sorry
