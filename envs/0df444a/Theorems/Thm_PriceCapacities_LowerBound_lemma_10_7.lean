-- Prove2me | Theorems.Thm_PriceCapacities_LowerBound_lemma_10_7
-- name    : PriceCapacities.LowerBound.lemma_10_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:21:35.445726+00:00
-- url     : https://prove2.me/theorems/231d417d-2d8e-40d0-a391-0a8a93c6fe02
-- title:
--   Lemma 10.7 — interpolating power differences recovers $u$ with relative error $C_\alpha2^{-M}$, with coefficient bounds (27)
-- statement:
--   Let $\alpha>0$. There is a constant $C_\alpha$, depending only on $\alpha$, such that for every $K_0>0$ and every integer $M\ge1$ there are $K_1,\dots,K_M\in[K_0,K_0M^2]$ and real coefficients $\gamma_1,\dots,\gamma_M$ such that, whenever $u\ge0$ and $|h|,|h-u|\le K_0/4$,
--   $$\Big|\sum_{\ell=1}^M\gamma_\ell\big((K_\ell+h)^\alpha-(K_\ell+h-u)^\alpha\big)-u\Big|\le C_\alpha2^{-M}u ,$$
--   and the coefficients satisfy
--   $$\sum_\ell|\gamma_\ell|K_\ell^\alpha\le C_\alpha K_0M^2,\qquad\sum_\ell|\gamma_\ell|\le C_\alpha K_0^{1-\alpha}M^2,\qquad\sum_\ell|\gamma_\ell|K_\ell^{\alpha-1}\le C_\alpha M .$$
--   The linear combination recovers the decrement $u$ of a squared distance from differences of $z$-th power costs ($\alpha=z/2$) up to exponentially small relative error; it is used in the measurement lemma 10.3. All powers are of positive numbers, since $K_\ell+h\ge3K_0/4$ and $K_\ell+h-u\ge3K_0/4$.
--
--   Differences from the source:
--
--   - encoding: ℓ = 1, …, M; 2^{−M} → ℓ : Fin M (0-based); ((2 : ℝ)^M)⁻¹; reason: same values
--   - reading: C_α in (26) and in each bound of (27) → one real constant C_α, chosen after α and before K_0, M, used in all four inequalities; reason: the printed C_α is a constant depending only on α; a common constant is the maximum of separate ones
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 36, Lemma 10.7, eqs. (26)–(27)

import Mathlib

namespace PriceCapacities.LowerBound

theorem lemma_10_7 (α : ℝ) (hα : 0 < α) :
    ∃ Cα : ℝ, ∀ K0 : ℝ, 0 < K0 → ∀ M : ℕ, 1 ≤ M →
      ∃ (K γ : Fin M → ℝ),
        (∀ l, K0 ≤ K l ∧ K l ≤ K0 * (M : ℝ) ^ 2) ∧
        (∀ u h : ℝ, 0 ≤ u → |h| ≤ K0 / 4 → |h - u| ≤ K0 / 4 →
          |∑ l, γ l * ((K l + h) ^ α - (K l + h - u) ^ α) - u| ≤ Cα * ((2 : ℝ) ^ M)⁻¹ * u) ∧
        ∑ l, |γ l| * K l ^ α ≤ Cα * K0 * (M : ℝ) ^ 2 ∧
        ∑ l, |γ l| ≤ Cα * K0 ^ (1 - α) * (M : ℝ) ^ 2 ∧
        ∑ l, |γ l| * K l ^ (α - 1) ≤ Cα * M := by sorry

end PriceCapacities.LowerBound
