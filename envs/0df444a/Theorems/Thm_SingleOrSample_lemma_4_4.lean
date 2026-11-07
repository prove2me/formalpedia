-- Prove2me | Theorems.Thm_SingleOrSample_lemma_4_4
-- name    : SingleOrSample.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:58.205188+00:00
-- url     : https://prove2.me/theorems/7b23055c-23ca-40b3-9936-4de24126f6d6
-- title:
--   Lemma 4.4 — deficit exponential moment
-- statement:
--   Let $k>0$, let $\sigma$ be any profile of legal strategies, each a function of the history so far, and let $w\ge0$ be weights with bundle sums $1$ for a labelling $P$ into $n$ bundles. Put $\psi(\lambda)=(e^\lambda-1)/k$ and let $r_j=j-t_j$ be the number of non-special rounds among the first $j$. For every $j<n$ and $\lambda\ge0$,
--   $$\mathbb E\bigl[\exp\bigl(\lambda D_j-\psi(\lambda)r_j\bigr)\bigr]\le1.$$
--   The expectation is over the coins of the first $j$ rounds. This is the central estimate: the deficit is controlled no matter how the earlier agents act.
--
--   Differences from the source:
--   - generalization: supporting prices → any weights w ≥ 0 with bundle sums 1; reason: the page's proof uses only these properties (and supporting prices have them by the milestone supporting_prices)
--   - encoding: j ∈ {0,…,i−1} for agent i ∈ [n] → j < n; reason: the union of those ranges over i
--   - encoding: the expectation → a sum in ℝ≥0∞ over histories; reason: nonnegative terms of a countable law
--   - encoding: preceding agents acting as arbitrary functions of the history → a profile of deterministic legal strategies, all quantified; reason: a randomized profile is a mixture, and the bound passes through mixtures
--   - encoding: the parameter k of Algorithm 2 in ψ(λ) = (e^λ − 1)/k → 0 < k; reason: nondegeneracy, ψ is undefined at k = 0
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 4.4, eq. (6), p.16

import Mathlib
import Definitions.Def_SingleOrSample_runLaw
import Definitions.Def_SingleOrSample_chainPrice
import Definitions.Def_SingleOrSample_deficit

namespace SingleOrSample

/-- **Lemma 4.4, deficit exponential moment** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma 4.4, p.16). For every profile of legal strategies,
each a function of the history, and all `j < n` and `λ ≥ 0`: `E[exp(λD_j − ψ(λ)r_j)] ≤ 1`, with
`ψ(λ) = (e^λ − 1)/k` and `r_j = j − t_j` the number of non-special rounds among the first `j`.

**Formalization Note.** The page's `j ≤ i − 1`, `i ∈ [n]`, is `j < n`. The expectation is a sum in `ℝ≥0∞`. The
weights are any nonnegative weights with bundle sums `1`, which is more general than supporting prices.
The page's "preceding agents" are the agents `0, …, j − 1`, whose strategies are the only ones that act. -/
theorem lemma_4_4 {m n k : ℕ} (hk : 0 < k) (σ : Fin n → Strategy m) (hσ : ∀ i, Legal n k (σ i))
    (P : Fin m → Fin n) (w : Fin m → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ b, ∑ e ∈ bundle P b, w e = 1)
    (ch : Hist m → Fin n) (hch : ∀ h, (activeBundles P ch h).Nonempty → ch h ∈ activeBundles P ch h)
    (j : ℕ) (hj : j < n) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∑' h, runLaw k σ j h *
      ENNReal.ofReal (Real.exp (lam * deficit P w ch h -
        ((Real.exp lam - 1) / (k : ℝ)) * ((j : ℝ) - (specialCount h : ℝ)))) ≤ 1 := by sorry

end SingleOrSample
