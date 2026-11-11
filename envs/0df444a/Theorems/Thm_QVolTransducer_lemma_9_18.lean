-- Prove2me | Theorems.Thm_QVolTransducer_lemma_9_18
-- name    : QVolTransducer.lemma_9_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:57.371553+00:00
-- url     : https://prove2.me/theorems/f303c0cb-2094-44ad-8618-2afa35b60b27
-- title:
--   Lemma 9.18 — the inverse cooling schedule has length $\tilde O(\sqrt d)$
-- statement:
--   Let $d\ge3$ be an integer, $R\ge1$, $\beta_0\ge d$, and let $(\beta_j)$ be the inverse cooling schedule $\beta_{j+1}=\beta_j(1-\max\{\frac1{8\sqrt d},\frac1{8R\sqrt{\beta_j}}\})$ if $\beta_j>\frac1{(2R)^2}$ and $\beta_{j+1}=0$ otherwise. Let
--
--   $$
--   \ell_1:=\min\{j\in\mathbb N:\beta_j\le d/R^2\},\qquad \ell_2:=\min\{j\in\mathbb N:\beta_{j+\ell_1}\le 1/(2R)^2\},
--   $$
--
--   with $\mathbb N=\{1,2,\dots\}$, and let $\ell$ be the first index with $\beta_\ell=0$. These minima exist, and:
--
--   1. for all $0\le a<b<\ell_1$: $\ b-a\le16\sqrt d\,\ln\frac{\beta_a}{\beta_b}$ and $\ \sum_{j=a}^{b-1}\frac1{\sqrt{\beta_j}}\le\frac{16\sqrt d}{\sqrt{\beta_{b-1}}}\ln\frac{\beta_a}{\beta_b}$ (15);
--   2. for all $\ell_1\le a<b<\ell_1+\ell_2$: $\ b-a\le16R\sqrt{\beta_a}\,\ln\frac{\beta_a}{\beta_b}$ and $\ \sum_{j=a}^{b-1}\frac1{\sqrt{\beta_j}}\le16R\ln\frac{\beta_a}{\beta_b}$ (16);
--   3. $\ell_1\le1+16\sqrt d\ln(\beta_0R^2/d)$, $\ell_2\le1+16\sqrt d\ln d$, and $\ell=\ell_1+\ell_2+1$.
--
--   The lemma bounds the number of stages of the volume algorithm and the sums that control its total transduction complexity.
--
--   Differences from the source:
--   - reading: ℓ = ℓ₁ + ℓ₂ + 1 with ℓ not defined in the lemma → ℓ is the least j with β_j = 0; reason: ℓ is the final value of j in Algorithm 2 ("While β_j > 0", p.71), the number of stages
--   - encoding: ℓ₁ := min{…}, ℓ₂ := min{…} over ℕ = {1, 2, …} → IsLeast over j ≥ 1, with the existence of the minima asserted; reason: the paper's ℕ starts at 1 (§2.1); the lemma's bounds presuppose the minima exist
--   - encoding: ℓ₁ ≤ 1 + 16√d ln(β₀R²/d) ∈ Õ(√d), ℓ₂ ≤ 1 + 16√d ln(d) ∈ Õ(√d), ℓ ∈ Õ(√d) → the explicit bounds only; reason: the Õ(√d) annotations are consequences of the explicit bounds (paper.md decision 11)
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Lemma 9.18, pp.64–65 (PDF pp.66–67)

import Mathlib
import Definitions.Def_QVolTransducer_coolSched

namespace QVolTransducer

/-- **Length of the inverse cooling schedule** (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Lemma 9.18, pp.64–65 (PDF pp.66–67)).

Let `d ≥ 3`, `R ≥ 1`, `β_0 ≥ d`, and let `β_j = coolSched d R β_0 j` be the schedule
`β_{j+1} = β_j (1 − max{1/(8√d), 1/(8R√β_j)})` if `β_j > 1/(2R)²`, else `0`. Let
`ℓ_1 = min{j ∈ ℕ : β_j ≤ d/R²}`, `ℓ_2 = min{j ∈ ℕ : β_{j+ℓ_1} ≤ 1/(2R)²}` (with `ℕ = {1,2,…}`),
and `ℓ` the first index with `β_ℓ = 0`. These minima exist, and
1. for `0 ≤ a < b < ℓ_1`: `b − a ≤ 16√d ln(β_a/β_b)` and
   `Σ_{j=a}^{b−1} 1/√β_j ≤ (16√d/√β_{b−1}) ln(β_a/β_b)` (15);
2. for `ℓ_1 ≤ a < b < ℓ_1 + ℓ_2`: `b − a ≤ 16R√β_a ln(β_a/β_b)` and
   `Σ_{j=a}^{b−1} 1/√β_j ≤ 16R ln(β_a/β_b)` (16);
3. `ℓ_1 ≤ 1 + 16√d ln(β_0R²/d)`, `ℓ_2 ≤ 1 + 16√d ln d`, and `ℓ = ℓ_1 + ℓ_2 + 1`.

**Formalization Note** The paper takes `ℕ = {1, 2, …}` (§2.1), so the minima range over `j ≥ 1`.
`ℓ` is the final value of `j` in Algorithm 2 (p.71), the first `j` with `β_j = 0`. The `∈ Õ(√d)`
annotations of the paper are the stated explicit bounds. -/
theorem lemma_9_18 (d : ℕ) (R β₀ : ℝ) (hd : 3 ≤ d) (hR : 1 ≤ R) (hβ₀ : (d : ℝ) ≤ β₀) :
    ∃ ℓ₁ ℓ₂ ℓ : ℕ,
      IsLeast {j : ℕ | 1 ≤ j ∧ coolSched d R β₀ j ≤ d / R ^ 2} ℓ₁ ∧
      IsLeast {j : ℕ | 1 ≤ j ∧ coolSched d R β₀ (j + ℓ₁) ≤ 1 / (2 * R) ^ 2} ℓ₂ ∧
      IsLeast {j : ℕ | coolSched d R β₀ j = 0} ℓ ∧
      (∀ a b : ℕ, a < b → b < ℓ₁ →
        ((b : ℝ) - a ≤ 16 * Real.sqrt d *
            Real.log (coolSched d R β₀ a / coolSched d R β₀ b) ∧
          ∑ j ∈ Finset.Ico a b, 1 / Real.sqrt (coolSched d R β₀ j) ≤
            16 * Real.sqrt d / Real.sqrt (coolSched d R β₀ (b - 1)) *
              Real.log (coolSched d R β₀ a / coolSched d R β₀ b))) ∧
      (∀ a b : ℕ, ℓ₁ ≤ a → a < b → b < ℓ₁ + ℓ₂ →
        ((b : ℝ) - a ≤ 16 * R * Real.sqrt (coolSched d R β₀ a) *
            Real.log (coolSched d R β₀ a / coolSched d R β₀ b) ∧
          ∑ j ∈ Finset.Ico a b, 1 / Real.sqrt (coolSched d R β₀ j) ≤
            16 * R * Real.log (coolSched d R β₀ a / coolSched d R β₀ b))) ∧
      (ℓ₁ : ℝ) ≤ 1 + 16 * Real.sqrt d * Real.log (β₀ * R ^ 2 / d) ∧
      (ℓ₂ : ℝ) ≤ 1 + 16 * Real.sqrt d * Real.log d ∧
      ℓ = ℓ₁ + ℓ₂ + 1 := by sorry

end QVolTransducer
