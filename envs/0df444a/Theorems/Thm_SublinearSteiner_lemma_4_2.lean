-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_2
-- name    : SublinearSteiner.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:19.090546+00:00
-- url     : https://prove2.me/theorems/0afd9bd3-0437-4412-8f96-47aa7f8f98c2
-- title:
--   Lemma 4.2 — the band statistic is sound
-- statement:
--   Let $Q_Q$ be an integer with $\omega^{-Q_Q}<\tau/2$, with the grid and covers of Lemma 4.1. For all subfamilies $F_i\subseteq\mathrm{comp}(G_{a_i}(N_i))$,
--   $$\sum_i\sum_{C\in F_i}D_i(C)\le Q_Q(L-\mathrm{OPT}).$$
--   So the total of any band scores is a valid discount on the MST weight.
--
--   Differences from the source:
--   - generalization: the grid (4.2) → any geometric grid a₀ ω^i with a₀ > 0; reason: (4.2) is the case a₀ = λ_f Θ ω^{−q₀}; the proof uses only the ratio ω
--   - encoding: Q_Q an integer → Q_Q a natural number; reason: the hypothesis forces Q_Q ≥ 1
--   - generalization: the floored metric of p.19 ("From now on we work with the floored metric") → any metric w on Fin n, with its own L and OPT; reason: the proof uses no property of the flooring; the floored metric is a metric (SublinearSteiner.floored), so the statement specializes to it
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.2, p.20

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.2 (The band statistic is sound), p.20. Let `Q_Q` be a fixed integer with `ω^{−Q_Q} < τ/2`. For all
subfamilies `F_i ⊆ C_i`, `Σ_i Σ_{C ∈ F_i} D_i(C) ≤ Q_Q (L − OPT)`.

**Formalization Note.** The grid and covers are as in Lemma 4.1. -/
theorem lemma_4_2 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (OPT L : ℝ)
    (hOPT : IsSteinerOpt T w OPT) (hL : IsTerminalMST T w L) (QQ : ℕ)
    (hQQ : omega ^ (-(QQ : ℤ)) < tau / 2) (a₀ : ℝ) (ha₀ : 0 < a₀) (I : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i, a i = a₀ * omega ^ i) (N : ℕ → Finset (Fin n)) (ρ : ℕ → ℝ)
    (hρ : ∀ i < I, 0 < ρ i ∧ ρ i ≤ delta * a i) (hN : ∀ i < I, IsCover w T (N i) (ρ i))
    (F : ℕ → Finset (Finset (Fin n))) (hF : ∀ i < I, F i ⊆ comp w (N i) (a i)) :
    ∑ i ∈ Finset.range I, ∑ C ∈ F i, bandScore w C (a i) (ρ i) ≤ QQ * (L - OPT) := by sorry

end SublinearSteiner
