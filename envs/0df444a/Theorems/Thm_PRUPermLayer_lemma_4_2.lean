-- Prove2me | Theorems.Thm_PRUPermLayer_lemma_4_2
-- name    : PRUPermLayer.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:50.320195+00:00
-- url     : https://prove2.me/theorems/ee02c531-8320-42a1-8d8d-b86220c67e16
-- title:
--   Lemma 4.2 — two-projector bound with Friedrichs cosine $c < 1$
-- statement:
--   Let $\Pi_1$ and $\Pi_2$ be orthogonal projectors with intersection projector $J$ and Friedrichs cosine at most $c < 1$.
--
--   1. For every $s > 0$,
--   $$
--   (1 - c^2)(I - J) \preceq (1 + cs)(I - \Pi_1) + (1 + c/s)(I - \Pi_2).
--   $$
--   2. Consequently, if a state $\sigma$ has $\mathrm{Tr}((I - \Pi_1)\sigma) \le a$ and $\mathrm{Tr}((I - \Pi_2)\sigma) \le b$, then
--   $$
--   \mathrm{Tr}((I - J)\sigma) \le \frac{a + b + 2c\sqrt{ab}}{1 - c^2}.
--   $$
--
--   The lemma replaces Gao's factor $4$ by a bound whose leading term is $a + b$, which gives the sharp constant of Theorem 1.1(ii). Both clauses are stated.
--
--   Differences from the source:
--   - encoding: orthogonal projectors $\Pi_1, \Pi_2$ and $J$ → projectors onto subspaces $K_1, K_2$ of $\mathbb C^\iota$ and onto $K_1 \cap K_2$; reason: an orthogonal projector is the projector onto its range
--   - encoding: $X \preceq Y$; $\mathrm{Tr}((I-\Pi)\sigma)$ → $Y - X$ positive semidefinite; real parts of the traces; reason: same order; the traces are real
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 4.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PRUPermLayer_friedrichsCos
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Lemma 4.2** (two-projector bound; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 4.2, p.18 (PDF p.20)). Let `Π₁, Π₂` be
orthogonal projectors with intersection projector `J` and Friedrichs cosine at most `c < 1`.
For every `s > 0`, `(1 − c²)(I − J) ⪯ (1 + cs)(I − Π₁) + (1 + c/s)(I − Π₂)`. Consequently, if a
state `σ` has `Tr((I − Π₁)σ) ≤ a` and `Tr((I − Π₂)σ) ≤ b`, then
`Tr((I − J)σ) ≤ (a + b + 2c√(ab))/(1 − c²)`.

**Formalization Note** `Π₁, Π₂, J` are the projectors onto subspaces `K₁, K₂, K₁ ∩ K₂` of `ℂ^ι`
(any finite `ι`). `X ⪯ Y` is `(Y − X).PosSemidef`. Real scalars act through `ℂ`. Traces of
`(I − Π)σ` are real; their real parts are compared. -/
theorem lemma_4_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (K₁ K₂ : Submodule ℂ (EuclideanSpace ℂ ι))
    (c : ℝ) (hc : friedrichsCos K₁ K₂ ≤ c) (hc1 : c < 1) :
    (∀ s : ℝ, 0 < s →
      ((((1 + c * s : ℝ) : ℂ) • (1 - projMat K₁) + ((1 + c / s : ℝ) : ℂ) • (1 - projMat K₂)) -
        ((1 - c ^ 2 : ℝ) : ℂ) • (1 - projMat (K₁ ⊓ K₂))).PosSemidef) ∧
    ∀ σ : Matrix ι ι ℂ, QAlgorithms.IsDensityMatrix σ → ∀ a b : ℝ,
      ((1 - projMat K₁) * σ).trace.re ≤ a → ((1 - projMat K₂) * σ).trace.re ≤ b →
        ((1 - projMat (K₁ ⊓ K₂)) * σ).trace.re ≤
          (a + b + 2 * c * Real.sqrt (a * b)) / (1 - c ^ 2) := by sorry

end PRUPermLayer
