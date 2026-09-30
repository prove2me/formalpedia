-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_complex_auxiliary_systems_of_bounded_grid_derivatives
-- name    : WeierstrassEllipticZeta.complex_auxiliary_systems_of_bounded_grid_derivatives
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T01:13:50.746498+00:00
-- url     : https://prove2.me/theorems/e8434cba-561c-4544-bfa4-eab92ac966ec
-- title:
--   Finite auxiliary systems from bounded nonzero derivatives
-- statement:
--   Let $L$ be a period pair with lattice $\Lambda$ and canonical Weierstrass functions $\wp,\zeta$. Fix complex numbers $\omega,u_1,u_2,\theta,\nu$, a bivariate integer polynomial $g$ of positive outer degree, and $d\in\mathbb Z[X]$ with $d(\theta)\ne0$. Assume the regular auxiliary-grid data, auxiliary-parameter estimates, $\zeta'=-\wp$ off the lattice, and the cleared zeta addition identity. No algebraic or transcendence assumption on $\theta,\nu$ is needed for this construction.
--
--   Use the actual parameters
--
--   $$m=\lfloor N/\log N\rfloor,\quad \ell=\lfloor\sqrt{N\log N}\rfloor,\quad
--   s=\lfloor N^{3/16}\rfloor,\quad q=\lfloor N^{5/8}\log N/64\rfloor,$$
--
--   the unshifted grids $\Gamma=\Gamma(s,s,q)$ and $\Gamma_3=\Gamma(3s,3s,3q)$, and $I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2$. Write
--
--   $$F_c(w)=\sum_{i\in I}c_iw^{i_0}\wp(w)^{i_1}\zeta(w)^{i_2}.$$
--
--   Assume `AuxiliaryGridJetMatrixData`: a constant $C$ such that for every integer derivative cutoff $K$, a constant $A>0$ gives, for all sufficiently large $N$, polynomial matrices $R(v,n,i)$ for $v\in\Gamma_3$, $n\le Km$, together with their nonlattice coordinate presentations. Their outer degrees are below $\deg_Yg$, inner degrees are bounded by $D\le Am$, and coefficient lengths by $e^{AN}$. The size bound $|I|(\deg_Yg+1)(D+1)\le e^{AN}$ and dimension gap $8(m+1)|\Gamma|\le|I|$ hold. Their evaluations are exactly the period-cleared monomial derivatives at lattice points and the eight-denominator-cleared translate derivatives at nonlattice points. At each point their common evaluated kernel is exactly the vanishing of all original derivatives through order $Km$. Matrices and presentations are chosen before the coefficient vector.
--
--   Assume also the following two uniform size estimates, conditional on the vanishing of all $F_c^{(j)}$ for $j<m+1$ on $\Gamma+u_1/2$, and of all derivatives below $n$ at $u_1/2+v$:
--
--   - For each real $B\ge0$, $K>0$, all sufficiently large $N$ give, for every coefficient vector with $|c_i|\le e^{BN}$, every $v\in\Gamma_3\cap\Lambda$, and $n\le Km$,
--     $$|d(\theta)^{7(m+2\ell+n)}F_c^{(n)}(u_1/2+v)|\le e^{-N^2\log N/147456}.$$
--   - For each presentation constant $C$, real $B\ge0$, $K>0$, all sufficiently large $N$ give, for every vector with $\sum_i|c_i|\le e^{BN}$, every $v\in\Gamma_3\setminus\Lambda$, every permitted eight-coordinate presentation $P$ at $(v,u_1/2)$, and $n\le Km$,
--     $$\left|\left(\prod_{a=0}^7E_a^{w_a}\right)[2(\wp(v)-\wp(u_1/2))]^{3\ell}F_c^{(n)}(u_1/2+v)\right|\le e^{-N^2\log N/147456},$$
--     where $E_a$ are its nonzero evaluated denominators and $(w_a)=(m,5\ell,5\ell,5\ell,m+5\ell+n,m+5\ell+n,m+5\ell+n,m+5\ell+n)$.
--
--   Finally assume the bounded nonzero-derivative estimate: there is an integer $K\ge1$ such that for all sufficiently large $N$, every nonzero coefficient vector $c\in\mathbb C^I$ has $F_c^{(n)}(u_1/2+v)\ne0$ for some $v\in\Gamma_3$ and $n\le Km$.
--
--   Then there are constants $a,c_0>0$ such that for all sufficiently large $N$ there is a `ComplexAuxiliarySystem` with coefficient budget $b=(3+|\theta|+|\nu|)a$, size and polynomial-height budget $a$, decay constant $c_0$, and outer degree strictly below $\deg_Yg$. Explicitly, it consists of finite polynomial linear equations and tests, with at least eight times as many columns as equations, polynomial degree and coefficient bounds prescribed by that structure, and the property that every nonzero complex vector of norm at most $e^{bN}$ in each coordinate satisfying the equations has a nonzero test value of norm at most $e^{-c_0N^2\log N}$. The equations and all tests precede the choice of that vector. One can take $c_0=1/147456$. The bounded nonzero-derivative estimate is an input, not a conclusion of this theorem.
-- source:
--   Senthil Kumar K (2026), Section 5, Lemmas 8–10 and equations (33)–(36), https://doi.org/10.1017/S001309152610145X. This conditional construction makes the equations and complete finite test family independent of the coefficient vector, using the existing arithmetic jet matrices and decay bounds. Lemma 9's bounded nonzero-derivative estimate remains an explicit input.

import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.complex_auxiliary_systems_of_bounded_grid_derivatives
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (hg : 0 < g.natDegree) (hd : Polynomial.aeval θ d ≠ 0)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_grid_matrices : AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d)
    (h_period_decay : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∀ i, ‖c i‖ ≤ Real.exp (B * N)) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω
            ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          v ∈ L.lattice → ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f (u₁ / 2 + v) = 0) →
            ‖(Polynomial.aeval θ d) ^ (7 * (m + 2 * l + n)) * iteratedDeriv n f (u₁ / 2 + v)‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456))
    (h_arithmetic_nonlattice_decay : ∀ (C : ℕ) (B K : ℝ), 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice →
            ∀ P : NonlatticeCoordinatePresentation L θ ν v (u₁ / 2) C N s,
              ∀ n : ℕ, (n : ℝ) ≤ K * m →
                (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
                ‖(∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
                    (P.denominator a) ^ nonlatticeJetWeight m l n a) *
                  (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^ (3 * l) *
                  iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                    Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456))
    (h_escape : ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          ∃ n : ℕ, n ≤ K * m ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by sorry
