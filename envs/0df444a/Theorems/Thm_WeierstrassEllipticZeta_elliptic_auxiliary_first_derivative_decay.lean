-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_auxiliary_first_derivative_decay
-- name    : WeierstrassEllipticZeta.elliptic_auxiliary_first_derivative_decay
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T23:24:22.443271+00:00
-- url     : https://prove2.me/theorems/1ad045d3-a668-4e42-b1a2-5ed66aae4ecf
-- title:
--   Decay of the first auxiliary derivative under sigma regularization
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$, canonical functions $\wp,\zeta$, and complex grid generators $\omega,u_1,u_2$. Assume regular auxiliary-grid data, auxiliary parameter data, translated-grid interpolation decay data, the identity $\zeta'=-\wp$ off $\Lambda$, and elliptic regularization data as defined in the mission.
--
--   Supply a normalized entire sigma differential datum $\sigma$, entire factors $S_0,S_1,S_2$ with $S_j=\sigma^{j+1}(\zeta,\wp,\wp')_j$ off the lattice, and a fixed $A>0$ such that all four entire functions have absolute value at most $\exp(A(1+|z|^2))$ at every complex $z$. Assume $\sigma$ is nonzero off $\Lambda$.
--
--   For any fixed real $B\ge0$ and $K>0$, all sufficiently large integers $N$ have the following property, uniformly in all subsequent choices. Put
--
--   $$m=\lfloor N/\log N\rfloor,\quad \ell=\lfloor\sqrt{N\log N}\rfloor,\quad
--   s=\lfloor N^{3/16}\rfloor,\quad q=\lfloor N^{5/8}\log N/64\rfloor,\quad
--   r=4q(|u_1|+|u_2|+|\omega|+1).$$
--
--   Let $I=\{0,\ldots,m\}\times\{0,\ldots,\ell\}^2$ and choose complex coefficients with $\sum_{i\in I}|c_i|\le e^{BN}$. Define
--
--   $$F(z)=\sum_{i\in I}c_i z^{i_0}\wp(z)^{i_1}\zeta(z)^{i_2}.$$
--
--   Suppose $F^{(j)}(x)=0$ for $0\le j<m+1$ at every
--
--   $$x=a_1u_1+a_2u_2+a_3\omega+u_1/2,\quad 0\le a_1,a_2<s,\quad0\le a_3<q.$$
--
--   Whenever $w\notin\Lambda$, $|w|+1\le2r$, and $|\sigma(w)^{3\ell}|^{-1}\le e^{N^2}$, every nonnegative integer $n\le Km$ satisfying $F^{(j)}(w)=0$ for $0\le j<n$ obeys
--
--   $$|F^{(n)}(w)|\le\exp\!\left(-N^2\log N/73728\right).$$
--
--   The threshold precedes the coefficient vector, evaluation point, and derivative order. The derivative need not be nonzero; order zero and the zero vector are included. This proves a conditional size estimate, not the existence of a bounded-order nonzero derivative. The fixed numerical decay constant belongs to this formalization.
-- source:
--   Senthil Kumar K (2026), Section 5, equations (30)–(33) and Lemma 6(i), https://doi.org/10.1017/S001309152610145X. The formal statement uses supplied regularization, growth and interpolation data, proves its own outer-circle bound, and imposes the reciprocal sigma estimate explicitly. The constant 1/73728 is a coarse formalization constant, not a quoted source constant.

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay

open Filter Set WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_auxiliary_first_derivative_decay
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_decay : AuxiliaryGridDecayData ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) (S : Fin 3 → ℂ → ℂ)
    (h_factors_entire : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (h_factors_eq : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = D.sigma z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (h_sigma_growth : ∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_factor_growth : ∀ (z : ℂ) (j : Fin 3),
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_sigma_nonzero : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0) :
    ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let r := 4 * (auxiliaryS3 N : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ w : ℂ, w ∉ L.lattice → ‖w‖ + 1 ≤ 2 * r →
          ‖D.sigma w ^ (3 * l)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) →
          ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f w = 0) →
            ‖iteratedDeriv n f w‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) := by sorry
