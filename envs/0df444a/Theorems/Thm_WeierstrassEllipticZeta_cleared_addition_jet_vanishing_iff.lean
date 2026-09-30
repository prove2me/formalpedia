-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_jet_vanishing_iff
-- name    : WeierstrassEllipticZeta.cleared_addition_jet_vanishing_iff
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T12:48:29.730441+00:00
-- url     : https://prove2.me/theorems/3a151161-eff2-4939-91b8-35686d21467d
-- title:
--   Clearing elliptic addition denominators preserves finite vanishing jets
-- statement:
--   Let $L$ be a complex period pair with lattice $\Omega$. Assume the canonical zeta derivative identity and the multiplied zeta addition identity at regular arguments. Let $z,v,z+v,z-v$ all lie outside $\Omega$.
--
--   For nonnegative integers $M,T$, a finite index set $I$, arbitrary nonnegative exponents $l_{0,i},l_{2,i},l_{3,i}$, and coefficients $c_i\in\mathbb C$, put
--
--   $$
--   F(w)=\sum_{i\in I}c_iw^{l_{0,i}}\wp(w)^{l_{2,i}}\zeta(w)^{l_{3,i}},
--   $$
--
--   $$
--   G_i(w)=(w+v)^{l_{0,i}}[2(\wp(v)-\wp(w))]^{3M}
--          \wp(w+v)^{l_{2,i}}\zeta(w+v)^{l_{3,i}}.
--   $$
--
--   Then the clearing factor is nonzero:
--
--   $$
--   [2(\wp(v)-\wp(z))]^{3M}\ne0,
--   $$
--
--   and finite vanishing jets are equivalent:
--
--   $$
--   \left(\forall\,0\le n<T,\ \sum_{i\in I}c_iG_i^{(n)}(z)=0\right)
--   \quad\Longleftrightarrow\quad
--   \left(\forall\,0\le n<T,\ F^{(n)}(z+v)=0\right).
--   $$
--
--   No a priori inequality between the elliptic values is assumed; it follows from the four regularity hypotheses and the addition identity. The statement includes $M=0$, $T=0$, empty index sets, and zero coefficient vectors. Exponents need not be bounded by $M$ for this analytic cancellation result. This is the local passage from cleared linear equations to ordinary derivative vanishing in the auxiliary-function construction.
-- source:
--   Senthil Kumar K (2026), Section 5, proof of Lemma 8, immediately after the definition of A(v,t): the order comparison between F and F_1 and the implication to equation (29). The formal statement makes the regularity hypotheses explicit, generalizes to an arbitrary finite monomial family, and proves the stronger equivalence of finite jets. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.LinearCombination

open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.cleared_addition_jet_vanishing_iff
    (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : z + v ∉ L.lattice) (hn : z - v ∉ L.lattice)
    (M T : ℕ) {ι : Type} [Fintype ι]
    (l₀ l₂ l₃ : ι → ℕ) (c : ι → ℂ) :
    (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) ≠ 0 ∧
    ((∀ n < T, ∑ i, c i *
        iteratedDeriv n (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i))
          z = 0) ↔
      ∀ n < T, iteratedDeriv n (fun w =>
        ∑ i, c i * w ^ l₀ i * L.weierstrassP w ^ l₂ i *
          weierstrassZeta L w ^ l₃ i) (z + v) = 0) := by sorry
