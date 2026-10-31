-- Prove2me | Theorems.Thm_SinkhornHall_lemma_1_1
-- name    : SinkhornHall.lemma_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:19.071766+00:00
-- url     : https://prove2.me/theorems/98f24428-5e92-4bc0-b249-efb214ada77c
-- title:
--   Lemma 1.1 — Pinsker's inequality for nonnegative vectors with equal sums
-- statement:
--   Let $p,q$ be nonnegative vectors indexed by a nonempty finite set with equal sums $p([n])=q([n])$, and let $D(p\|q)$ be their KL divergence (with $x\log\frac x0=\infty$). Then
--
--   $$D(p\|q)\ \ge\ \frac{1}{2\,p([n])}\,\|p-q\|_1^2 .$$
--
--   This is Pinsker's inequality in unnormalized form. In the analysis of the Sinkhorn algorithm it converts the exact decrement of $\log\kappa$ (Lemma 2.4) into a decrement proportional to the squared $\ell_1$ error of the current marginals.
--
--   **Formalization Note** The right side is computed in $\mathbb R$ and cast to `EReal`. When $p([n])=0$ the fraction is undefined in the paper; then $p=q=0$, Lean's division by zero gives $0$, and both sides are $0$.
--
--   Differences from the source:
--   - encoding: D(p∥q) ∈ ℝ ∪ {∞} → klDiv p q : EReal; reason: Lean convention; same values
--   - encoding: 1/(2p([n])) undefined when p([n]) = 0 → Lean's x / 0 = 0, so the left side is 0; reason: the case p([n]) = 0 forces p = q = 0, where both sides are 0; no instance with a defined left side changes
--   - encoding: [n] for a positive integer n → a nonempty finite index type ι; reason: any such type is in bijection with some [n]
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 1.1, (1.1), p.4 (cited from [8, Lemma 11.6.1])

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Lemma 1.1 (Pinsker's inequality).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 1.1, (1.1), p.4: "For nonnegative vectors
p, q ∈ ℝⁿ with p([n]) = q([n]), D(p∥q) ≥ (1/(2p([n]))) ∥p − q∥₁²."

**Formalization Note.** `D` is `klDiv` (valued in `EReal`, `⊤` when some `qᵢ = 0 < pᵢ`); the left
side `‖p − q‖₁² / (2 p([n]))` is a real number cast to `EReal`. When `p([n]) = 0` the paper's
fraction is undefined; then `p = q = 0`, Lean's `/ 0` gives `0`, and both sides are `0`. The index
set is a nonempty finite type (the paper's `[n]` for a positive integer `n`, p.4). -/
theorem lemma_1_1 {ι : Type*} [Fintype ι] [Nonempty ι] (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, p i = ∑ i, q i) :
    (((∑ i, |p i - q i|) ^ 2 / (2 * ∑ i, p i) : ℝ) : EReal) ≤ klDiv p q := by sorry

end SinkhornHall
