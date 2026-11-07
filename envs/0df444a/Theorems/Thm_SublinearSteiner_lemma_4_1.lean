-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_1
-- name    : SublinearSteiner.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:45:48.6462+00:00
-- url     : https://prove2.me/theorems/42324de0-728d-485a-ad35-c80fc8a937d4
-- title:
--   Lemma 4.1 — the saving is sound
-- statement:
--   Let $Q_S$ be an integer with $\frac54\omega^{-Q_S}<1-2\delta$. Let $a_i=a_0\omega^i$, $0\le i<I$, and let $N_i\subseteq T$ be a $\rho_i$-cover of $T$ with $0<\rho_i\le\delta a_i$. With $\Phi_i$ the saving of the components of $G_{a_i}(N_i)$,
--   $$\sum_ia_i\Phi_i\le32Q_S(L-\mathrm{OPT}).$$
--   So the scale-weighted saving is a valid discount on the MST weight.
--
--   Differences from the source:
--   - generalization: the grid (4.2) → any geometric grid a₀ ω^i with a₀ > 0; reason: (4.2) is the case a₀ = λ_f Θ ω^{−q₀}; the proof uses only the ratio ω
--   - encoding: Q_S an integer → Q_S a natural number; reason: the hypothesis forces Q_S ≥ 1
--   - generalization: the floored metric of p.19 ("From now on we work with the floored metric") → any metric w on Fin n, with its own L and OPT; reason: the proof uses no property of the flooring; the floored metric is a metric (SublinearSteiner.floored), so the statement specializes to it
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.1, p.20

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.1 (The saving is sound), p.20. Let `Q_S` be a fixed integer with `(5/4) ω^{−Q_S} < 1 − 2δ`. Then
`Σ_i a_i Φ_i ≤ 32 Q_S (L − OPT)`.

**Formalization Note.** The grid is any geometric grid `a_i = a₀ ω^i`, `0 ≤ i < I`, which contains (4.2). `N_i` is any `ρ_i`-cover
with `0 < ρ_i ≤ δ a_i`. The hypothesis forces `Q_S ≥ 1`, so `Q_S` is a natural number. -/
theorem lemma_4_1 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (OPT L : ℝ)
    (hOPT : IsSteinerOpt T w OPT) (hL : IsTerminalMST T w L) (QS : ℕ)
    (hQS : 5 / 4 * omega ^ (-(QS : ℤ)) < 1 - 2 * delta) (a₀ : ℝ) (ha₀ : 0 < a₀) (I : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i, a i = a₀ * omega ^ i) (N : ℕ → Finset (Fin n)) (ρ : ℕ → ℝ)
    (hρ : ∀ i < I, 0 < ρ i ∧ ρ i ≤ delta * a i) (hN : ∀ i < I, IsCover w T (N i) (ρ i)) :
    ∑ i ∈ Finset.range I, a i * (coverSaving w (N i) (a i) : ℝ) ≤ 32 * QS * (L - OPT) := by sorry

end SublinearSteiner
