-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_4_6
-- name    : SmoothBerr.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:00:52.247651+00:00
-- url     : https://prove2.me/theorems/40acc3c6-3e92-4def-a3af-1177574d7b9c
-- title:
--   Theorem 4.6 — hardness of approximation with odd polynomials: degree $\gtrsim\min\{n,\log(\kappa)/\varepsilon\}$
-- statement:
--   There are universal constants such that the following holds whenever $n\gtrsim1$, $\kappa\gtrsim1$ and $\kappa^{-0.1}\lesssim\varepsilon\lesssim1$. There exist weights $w_1,\dots,w_n\in[0,1]$ and nodes $1\ge\sigma_1\ge\sigma_2\ge\dots\ge\sigma_n\ge1/\kappa$ such that every odd polynomial $p$ satisfying
--   $$
--   \sum_{i=1}^n w_i\bigl(\sigma_ip(\sigma_i)-1\bigr)^2\ \le\ \sigma_1^2\varepsilon^2\sum_{i=1}^n w_i\,p(\sigma_i)^2 \tag{20}
--   $$
--   has degree at least $t\gtrsim\min\{n,\log(\kappa)/\varepsilon\}$.
--
--   By Lemma 4.5, the left side divided by $\sigma_1^2\sum_iw_ip(\sigma_i)^2$ is the squared backward error of a vector of a normal-equations Krylov subspace on a matrix with singular values $\sigma_i$; the theorem therefore exhibits a spectrum on which no such Krylov vector of low degree has backward error $\varepsilon$.
--
--   **Formalization Note** All constants ($n\ge N_0$, $\kappa\ge K_0$, $\kappa^{-0.1}\le a\varepsilon$, $\varepsilon\le b'$, and the constant $c$ of the conclusion) are chosen first. A polynomial is odd if $p(-x)=-p(x)$ for all $x$; its degree is its natural degree.
--
--   Differences from the source:
--   - reading: nodes σ₁, …, σₙ ∈ [1/κ, 1] with σ₁ on the right of (20) → nodes sorted decreasingly (Antitone σ), σ₁ = σ at index 0 the largest; reason: σ₁ in (20) is the largest singular value, as in Lemma 4.5 (σ₁ ≥ … ≥ σₙ) and the proof on p.21; requiring sorted nodes makes the existential claim stronger, and with unsorted nodes σ₁ could be the smallest node
--   - reading: weights w_i ≥ 0 (p.7) or w_i ∈ [0, 1] (p.19) → weights w_i ∈ [0, 1]; reason: the restated form of p.19, the stronger of the two
--   - encoding: n ≳ 1, κ ≳ 1, κ^{−0.1} ≲ ε ≲ 1; degree ≳ min{n, log(κ)/ε} → ∃ N₀ K₀ a b' c (a, b', c > 0) first; n ≥ N₀ and n ≥ 1, κ ≥ K₀, κ^{−0.1} ≤ a·ε, ε ≤ b'; c·min{n, log κ/ε} ≤ natDegree p; reason: §3, p.4: ≲ hides a universal constant; n ≥ 1 makes σ₁ exist and is implied by choosing N₀ ≥ 1
--   - encoding: odd polynomial p → p : ℝ[X] with p.eval (−x) = −p.eval x for all x; reason: the same polynomials
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 4.6, p.7; restated with weights in [0, 1], p.19

import Mathlib

open Polynomial

namespace SmoothBerr.Supplement

/-- **Theorem 4.6, restated (Hardness of approximation with odd polynomials)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 4.6, p.7; restated p.19).

Fix `n ≳ 1`, `κ ≳ 1` and `κ^{−0.1} ≲ ε ≲ 1`. There exist weights `w_1, …, w_n ∈ [0, 1]` and
nodes `σ_1, …, σ_n ∈ [1/κ, 1]` such that every odd polynomial `p` with
`∑ w_i (σ_i p(σ_i) − 1)² ≤ σ_1² ε² ∑ w_i p(σ_i)²` (20) has degree `≳ min{n, log(κ)/ε}`.

**Formalization Note**
1. Every `≲`/`≳` is a universal constant chosen first (`N₀, K₀, a, b', c`), before `n`, `κ`,
   `ε`: `n ≥ N₀` (and `n ≥ 1`, so that `σ_1` exists), `κ ≥ K₀`, `κ^{−0.1} ≤ a ε`, `ε ≤ b'`;
   the conclusion is `c · min{n, log κ/ε} ≤ deg p`.
2. The nodes are sorted decreasingly, `σ_1 ≥ … ≥ σ_n` (index `0` is `σ_1`), as in Lemma 4.5 and
   the proof on p.21; the weights lie in `[0, 1]` as on p.19.
3. "Odd" is `p(−x) = −p(x)` for all `x`; the degree is `natDegree`. -/
theorem theorem_4_6 :
    ∃ N₀ K₀ a b' c : ℝ, 0 < a ∧ 0 < b' ∧ 0 < c ∧
      ∀ (n : ℕ) (hn : 0 < n) (κ ε : ℝ), N₀ ≤ n → K₀ ≤ κ → κ ^ (-(1 / 10 : ℝ)) ≤ a * ε →
        ε ≤ b' →
        ∃ w σ : Fin n → ℝ, (∀ i, w i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, σ i ∈ Set.Icc (1 / κ) 1) ∧
          Antitone σ ∧
          ∀ p : ℝ[X], (∀ x : ℝ, p.eval (-x) = -p.eval x) →
            ∑ i, w i * (σ i * p.eval (σ i) - 1) ^ 2 ≤
              σ ⟨0, hn⟩ ^ 2 * ε ^ 2 * ∑ i, w i * p.eval (σ i) ^ 2 →
            c * min (n : ℝ) (Real.log κ / ε) ≤ p.natDegree := by sorry

end SmoothBerr.Supplement
