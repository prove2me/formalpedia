-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth
-- name    : WeierstrassEllipticZeta.cleared_addition_entire_growth
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T14:06:19.960847+00:00
-- url     : https://prove2.me/theorems/877458bf-58f8-4b87-99ef-adaa576271d2
-- title:
--   Entire extension and explicit growth of translated, cleared elliptic auxiliary sums
-- statement:
--   Let $L$ be a complex period pair, with lattice $\Omega$ and canonical functions $\zeta,\wp,\wp'$. Assume their multiplied addition identities at regular arguments. Supply entire functions $\sigma,S_0,S_1,S_2$ satisfying
--
--   $$S_0=\sigma\zeta,\qquad S_1=\sigma^2\wp,\qquad S_2=\sigma^3\wp'
--   \qquad\text{outside }\Omega.$$
--
--   Let $I$ be any finite index set, let $v\notin\Omega$, and choose complex coefficients $c_i$ and nonnegative integers $\ell_{0i},\ell_{2i},\ell_{3i},D,M$ with
--
--   $$\ell_{0i}\le D,\qquad\ell_{2i},\ell_{3i}\le M.$$
--
--   Define the translated, cleared auxiliary sum
--
--   $$f(z)=\sum_{i\in I}c_i(z+v)^{\ell_{0i}}
--   [2(\wp(v)-\wp(z))]^{3M}\wp(z+v)^{\ell_{2i}}\zeta(z+v)^{\ell_{3i}}.$$
--
--   There exists a single entire function $G$, chosen before any radius or bounds, with
--
--   $$G(z)=\sigma(z)^{15M}f(z)\qquad(z,z+v\notin\Omega).$$
--
--   Put
--
--   $$V_v=1+|\zeta(v)|+|\wp(v)|+|\wp'(v)|,\qquad K_v=36V_v^3.$$
--
--   For every $R\in\mathbb R$ and $B\ge1$, if all four basic entire functions are bounded in absolute value by $B$ on $|z|\le R$, then
--
--   $$|G(z)|\le C_R:=\left(\sum_i|c_i|\right)
--   \max(1,R+|v|)^D K_v^{15M}B^{90M}\qquad(|z|\le R).$$
--
--   The finite set may be empty, coefficients may vanish, and $D=M=0$ is allowed. Neither $\sigma$ nor the addition factor is assumed nonzero. The identity is restricted to regular arguments; the entire extension supplies its own values at poles. This is a conditional version of the construction in Lemma 6(ii), with a coarse explicit growth constant. It does not construct the basic sigma factors or assert the source's sharper displayed numerical bound.
-- source:
--   Supporting conditional formulation of Senthil Kumar K (2026), Section 4, Lemma 6(ii), its proof and equation (16), using the multiplied addition formulas (5)-(7). The regularizer exponent 15M is unchanged; the disk bound uses the explicit coarse constant K_v^(15M) B^(90M), not the sharper source constant. Basic entire sigma factors are hypotheses. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Tactic.FinCases

open Finset Set WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.cleared_addition_entire_growth
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
            (36 * (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ +
              ‖L.derivWeierstrassP v‖) ^ 3) ^ (15 * M) * B ^ (90 * M) := by sorry
