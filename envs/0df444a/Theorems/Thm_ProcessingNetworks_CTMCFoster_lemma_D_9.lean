-- Prove2me | Theorems.Thm_ProcessingNetworks_CTMCFoster_lemma_D_9
-- name    : ProcessingNetworks.CTMCFoster.lemma_D_9
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:27:25.154717+00:00
-- url     : https://prove2.me/theorems/b7d7b8af-1563-4d4f-bde9-b0a5521ff9ab
-- title:
--   Lemma D.9 — invariant measures of a generator and of its jump matrix
-- statement:
--   Let $\Lambda$ be a generator matrix on a countable set $\mathscr S$ with exit rates $\lambda(i)=-\Lambda_{ii}>0$ and jump matrix $G$, let $\eta$ be a measure on $\mathscr S$, and define $\mu(i)=\lambda(i)\eta(i)$ for $i\in\mathscr S$. Then
--
--   $$
--   \eta\Lambda=0\quad\Longleftrightarrow\quad \mu G=\mu,
--   $$
--
--   each row product being a convergent series. The lemma gives a one-to-one correspondence between invariant measures of the continuous-time chain and invariant measures of its jump chain.
--
--   Differences from the source:
--   - generalization: a (regular) generator, i.e. (D.2) and non-explosive → a generator with (D.2), non-explosion not assumed; reason: the verification is algebraic, and every regular generator satisfies the Lean hypothesis
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Lemma D.9, eq. (D.18), p.291 (PDF 307)

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_ProcessingNetworks_CTMCFoster_IsInvariantMeasure

namespace ProcessingNetworks.CTMCFoster

open MatrixAnalytic.ProductForm

/-- Lemma D.9. Let `Λ` be a generator with jump matrix `G`, let `η` be a measure on `S` and put
`μ(i) = λ(i) η(i)` (D.18). Then `η` is invariant for `Λ` if and only if `μ G = μ`.

Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Lemma D.9,
eq. (D.18), p.291 (PDF 307).

**Formalization Note** `holdRate Λ i` is `λ(i)` and `jumpP Λ` is `G`. `μ G = μ` is the convergence
of `∑_x μ(x) G(x, y)` to `μ(y)` for each `y`. The book's "(regular)" is parenthetical: non-explosion
is not assumed here. -/
theorem lemma_D_9 {S : Type*} [Countable S] [DecidableEq S] {Λ : S → S → ℝ}
    (hΛ : IsGeneratorC Λ) (η μ : S → ℝ) (hη : ∀ i, 0 ≤ η i)
    (hμ : ∀ i, μ i = holdRate Λ i * η i) :
    IsInvariantMeasure Λ η ↔ ∀ y, HasSum (fun x => μ x * jumpP Λ x y) (μ y) := by sorry

end ProcessingNetworks.CTMCFoster
