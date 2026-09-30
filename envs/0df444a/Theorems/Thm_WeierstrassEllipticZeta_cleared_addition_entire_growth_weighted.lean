-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth_weighted
-- name    : WeierstrassEllipticZeta.cleared_addition_entire_growth_weighted
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T23:51:02.25811+00:00
-- url     : https://prove2.me/theorems/72ce90a9-d4de-4927-b701-7638d4fbae07
-- title:
--   Weighted growth bound for the cleared elliptic addition sum
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical functions $\wp,\zeta$. Assume their multiplied addition identities for regular $z,v,z+v$:
--
--   $$2(\wp(v)-\wp(z))\zeta(z+v)=2(\zeta(z)+\zeta(v))(\wp(v)-\wp(z))+\wp'(v)-\wp'(z),$$
--
--   $$4(\wp(v)-\wp(z))^2\wp(z+v)=-4(\wp(z)+\wp(v))(\wp(v)-\wp(z))^2+(\wp'(v)-\wp'(z))^2.$$
--
--   Supply entire functions $\sigma,S_0,S_1,S_2$ such that $S_0=\sigma\zeta$, $S_1=\sigma^2\wp$ and $S_2=\sigma^3\wp'$ outside the lattice. Let $I$ be any finite index set, $v\notin\Lambda$, $c_i\in\mathbb C$, and let $d_i,b_i,e_i,D,M$ be nonnegative integers with $d_i\le D$ and $b_i,e_i\le M$. Put
--
--   $$f(z)=\sum_{i\in I}c_i(z+v)^{d_i}[2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{b_i}\zeta(z+v)^{e_i}.$$
--
--   There is an entire function $G$, chosen before any radius or bounds, satisfying
--
--   $$G(z)=\sigma(z)^{15M}f(z)\qquad(z,z+v\notin\Lambda).$$
--
--   Write $V=1+|\zeta(v)|+|\wp(v)|+|\wp'(v)|$. For every real radius $R$ and $B\ge1$ bounding all four entire functions on $|z|\le R$, the same $G$ obeys
--
--   $$|G(z)|\le\left(\sum_{i\in I}|c_i|\right)\max(1,R+|v|)^D\,36^{3M}V^{5M}B^{15M}
--   \qquad(|z|\le R).$$
--
--   The moving-coordinate exponent is $5M$, obtained by retaining the separate degrees of the three cleared addition factors. The entire-factor exponent is $15M$. Empty finite sets, zero coefficients and $M=0$ are included; neither sigma nor the addition factor is assumed nonzero. The identity only applies at regular arguments, while the entire extension defines its own values at poles. The numerical constant is an explicit choice for this formalization.
-- source:
--   Senthil Kumar K (2026), Section 4, proof of Lemma 6(ii), equation (16) and its adjacent degree bound max(sum mu, sum rho)<=5L2, https://doi.org/10.1017/S001309152610145X. The proof keeps separate weights in the three multiplied addition factors and obtains the explicit bound 36^(3M)*V^(5M)*B^(15M). The numerical constant is a formalization choice, not a quoted source constant.

import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire

open Set WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.cleared_addition_entire_growth_weighted
    (L : PeriodPair)
    (hZ : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (hP : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (hσ : AnalyticOnNhd ℂ σ univ) (hS : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (hrel : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = σ z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    {ι : Type} [Fintype ι] (v : ℂ) (hv : v ∉ L.lattice)
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (D M : ℕ)
    (h₀ : ∀ i, l₀ i ≤ D) (h₂ : ∀ i, l₂ i ≤ M) (h₃ : ∀ i, l₃ i ≤ M) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        G z = σ z ^ (15 * M) * ∑ i, c i *
          clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) z) ∧
      ∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D *
            (36 : ℝ) ^ (3 * M) *
            (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ +
              ‖L.derivWeierstrassP v‖) ^ (5 * M) * B ^ (15 * M) := by sorry
