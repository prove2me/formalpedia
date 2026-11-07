-- Prove2me | Theorems.Thm_SoftmaxAttnFD_eq_7_5_lemma_7_10
-- name    : SoftmaxAttnFD.eq_7_5_lemma_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:43.616704+00:00
-- url     : https://prove2.me/theorems/ba3b9b9e-aa13-4bd2-814c-549311a559ee
-- title:
--   (7.5) and Lemma 7.10, p.33 — balanced parameters and heavy cells
-- statement:
--   Let $k\ge2$ and $m,n\ge1$ with $m^k>n$, $n^k>m$. Put $\Phi(m,n)=(mn)^{k/(k+1)}$, $\kappa_0=(m^k/n)^{1/(k^2-1)}$, $\kappa=\lceil\kappa_0\rceil$, $n_\kappa=n/\kappa$, $\Gamma=4^{k+1}$. Then $n\kappa_0^{k-1}=m(n/\kappa_0)^{(k-1)/k}=\Phi(m,n)$, and
--   $$2\le\kappa\le\min\{2\kappa_0,n\},\quad\Phi(m,n)>\max\{m,n\},\quad n\kappa^{k-1}\le2^{k-1}\Phi(m,n),\quad m(n/\kappa)^{(k-1)/k}\le\Phi(m,n).$$
--   Moreover, let $(m_\Delta,n_\Delta)_{\Delta\in D}$ be a finite list of pairs of positive integers with $\sum_\Delta m_\Delta\le m$ and $n_\Delta\le n_\kappa$. Call $\Delta$ heavy if $m_\Delta>\Gamma n_\kappa^{1/k}$. Then
--   $$\sum_{\Delta\text{ heavy}}\Phi(m_\Delta,n_\Delta)\le\frac14\Phi(m,n),\qquad\sum_{\Delta\text{ heavy}}(m_\Delta+n_\Delta)\le(1+\Gamma^{-1})\Phi(m,n),$$
--   and $m_\Delta n_\Delta\le mn/2$ for every $\Delta\in D$. These bounds make the recursion's potential decay geometrically.
--
--   Differences from the source:
--   - encoding: "balanced sizes m, n" with k ≥ 2 stated in the text → hypotheses 2 ≤ k, 1 ≤ m, 1 ≤ n, n < m^k, m < n^k; reason: the page says "Otherwise k ≥ 2", and balanced positive sizes force it
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), (7.5) and Lemma 7.10, p.33

import Definitions.Def_SoftmaxAttnFD_F

namespace SoftmaxAttnFD

open Classical in
/-- **(7.5) and Lemma 7.10** (arXiv:2611.06055, sha256 a60f7609…, p.33). For balanced sizes
`m^k > n`, `n^k > m`, with `κ₀ = (m^k/n)^{1/(k²−1)}`, `κ = ⌈κ₀⌉`, `n_κ = n/κ`, `Γ = 4^{k+1}`: the bounds
of (7.5), and the bounds on heavy cells.

**Formalization Note** `2 ≤ k` is the page's "Otherwise k ≥ 2" (p.33), which balanced sizes `m, n ≥ 1`
already force. `n_κ` is the real quotient, as printed, not a floor. The "finite list" is a `Finset` of
indices. -/
theorem eq_7_5_lemma_7_10 (k m n : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmk : n < m ^ k) (hnk : m < n ^ k) (κ₀ : ℝ)
    (hκ₀ : κ₀ = ((m : ℝ) ^ k / n) ^ (1 / ((k : ℝ) ^ 2 - 1))) (κ : ℕ) (hκ : κ = ⌈κ₀⌉₊)
    (nκ : ℝ) (hnκ : nκ = (n : ℝ) / κ) (Γ : ℝ) (hΓ : Γ = 4 ^ (k + 1)) :
    (n : ℝ) * κ₀ ^ (k - 1) = Phi k m n ∧
    (m : ℝ) * ((n : ℝ) / κ₀) ^ (((k : ℝ) - 1) / k) = Phi k m n ∧
    2 ≤ κ ∧ (κ : ℝ) ≤ 2 * κ₀ ∧ κ ≤ n ∧
    (m : ℝ) < Phi k m n ∧ (n : ℝ) < Phi k m n ∧
    (n : ℝ) * (κ : ℝ) ^ (k - 1) ≤ 2 ^ (k - 1) * Phi k m n ∧
    (m : ℝ) * ((n : ℝ) / κ) ^ (((k : ℝ) - 1) / k) ≤ Phi k m n ∧
    ∀ {ι : Type} (D : Finset ι) (mΔ nΔ : ι → ℕ),
      (∀ Δ ∈ D, 1 ≤ mΔ Δ ∧ 1 ≤ nΔ Δ) → ∑ Δ ∈ D, mΔ Δ ≤ m → (∀ Δ ∈ D, (nΔ Δ : ℝ) ≤ nκ) →
      ∑ Δ ∈ D.filter (fun Δ => Γ * nκ ^ (1 / (k : ℝ)) < mΔ Δ), Phi k (mΔ Δ) (nΔ Δ) ≤
          (1 / 4) * Phi k m n ∧
      ∑ Δ ∈ D.filter (fun Δ => Γ * nκ ^ (1 / (k : ℝ)) < mΔ Δ), ((mΔ Δ : ℝ) + nΔ Δ) ≤
          (1 + Γ⁻¹) * Phi k m n ∧
      ∀ Δ ∈ D, ((mΔ Δ : ℝ) * nΔ Δ) ≤ (m : ℝ) * n / 2 := by sorry

end SoftmaxAttnFD
