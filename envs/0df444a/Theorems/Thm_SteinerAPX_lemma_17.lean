-- Prove2me | Theorems.Thm_SteinerAPX_lemma_17
-- name    : SteinerAPX.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:59.264349+00:00
-- url     : https://prove2.me/theorems/e7c1b323-da2b-4c23-acb3-71665e178935
-- title:
--   Lemma 17 — $\mathrm{OPT}(P)\le\mathrm{OPT}(Q)\le\lambda\,\mathrm{OPT}(P)$ when $\|p_i-p_j\|\le\|q_i-q_j\|\le\lambda\|p_i-p_j\|$
-- statement:
--   Let $P=\{p_1,\dots,p_n\}\subseteq\mathbb R^D$ and $Q=\{q_1,\dots,q_n\}\subseteq\mathbb R^{D'}$ be finite point sets in Euclidean spaces of possibly different dimensions, and let $\lambda\ge1$. If
--   $$
--   \|p_i-p_j\|\le\|q_i-q_j\|\le\lambda\|p_i-p_j\|\qquad\text{for all } i,j,
--   $$
--   then
--   $$
--   \mathrm{OPT}(P)\le\mathrm{OPT}(Q)\le\lambda\,\mathrm{OPT}(P).
--   $$
--
--   With display (3), this transfers the gap of Lemma 16 to logarithmic dimension.
--
--   Differences from the source:
--   - encoding: point sets P = {p₁, …, pₙ}, Q = {q₁, …, qₙ} → the ranges of indexed families p : Fin n → ℝᴰ, q : Fin n → ℝᴰ′; reason: the index pairs the points as the hypothesis does
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 17, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SteinerAPX_Network

namespace SteinerAPX

/-- **Lemma 17 (Steiner optimum under bi-Lipschitz maps of the terminals).** S. Bartlmae,
*Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256
6f78a9ea…), Lemma 17, p.22 (PDF p.24): "Let P = {p1, …, pn} and Q = {q1, …, qn} be finite point
sets in Euclidean spaces of possibly different dimensions. If, for some λ ≥ 1, their pairwise
distances satisfy ∥pi − pj∥ ≤ ∥qi − qj∥ ≤ λ∥pi − pj∥ for all i, j, then
OPT(P) ≤ OPT(Q) ≤ λ OPT(P)."

For points `p₁, …, pₙ ∈ ℝᴰ`, `q₁, …, qₙ ∈ ℝᴰ'` and `λ ≥ 1` with
`‖pᵢ − pⱼ‖ ≤ ‖qᵢ − qⱼ‖ ≤ λ‖pᵢ − pⱼ‖` for all `i, j`:
`OPT({pᵢ}) ≤ OPT({qᵢ}) ≤ λ · OPT({pᵢ})`.

**Formalization Note** The point sets are the ranges of the indexed families `p, q : Fin n → ℝᴰ`,
`ℝᴰ'`. `OPT` is `opt`. -/
theorem lemma_17 {ι ι' : Type} [Fintype ι] [Fintype ι'] {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ ι) (q : Fin n → EuclideanSpace ℝ ι') (lam : ℝ) (hlam : 1 ≤ lam)
    (h : ∀ i j, dist (p i) (p j) ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ lam * dist (p i) (p j)) :
    opt (Set.range p) ≤ opt (Set.range q) ∧ opt (Set.range q) ≤ lam * opt (Set.range p) := by sorry

end SteinerAPX
