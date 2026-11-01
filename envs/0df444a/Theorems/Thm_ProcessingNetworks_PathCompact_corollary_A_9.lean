-- Prove2me | Theorems.Thm_ProcessingNetworks_PathCompact_corollary_A_9
-- name    : ProcessingNetworks.PathCompact.corollary_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:09.457806+00:00
-- url     : https://prove2.me/theorems/73f45e5f-a74b-423a-8964-5fc19c523ec9
-- title:
--   Corollary A.9 — equi-Lipschitz paths from $0$ have a u.o.c. convergent subsequence
-- statement:
--   Fix an integer $d>0$. Let $A\subset C^d$ be a set of continuous paths $x:\mathbb R_+\to\mathbb R^d$ such that
--
--   1. $x(0)=0$ for every $x\in A$, and
--   2. $A$ is equi-Lipschitz: there is a constant $L>0$ with
--   $$\sup_{x\in A}|x(t)-x(s)|\le L|t-s|\qquad\text{for all }s,t\in\mathbb R_+,$$
--   where $|\cdot|$ is the $\ell^1$ norm on $\mathbb R^d$.
--
--   Then for every sequence $\{x_n\}\subset A$ there exist a subsequence $\{x_{n_k}\}$ and a path $y\in C^d$ with $x_{n_k}\to y$ u.o.c.
--
--   The corollary extends the Arzelà–Ascoli theorem from a compact interval to $\mathbb R_+$ by a diagonal argument; it is the compactness principle used in the book to extract u.o.c. convergent subsequences of equi-Lipschitz paths.
--
--   Differences from the source:
--   - encoding: time set ℝ₊, index set ℕ = {1, 2, …}, a subsequence {n_k} → ℝ≥0, ℕ (from 0), a strictly increasing φ : ℕ → ℕ; reason: Lean convention; same instances
--   - encoding: |·| the ℓ¹ norm on ℝ^d in (A.2) and in u.o.c. convergence → Fin d → ℝ with (A.2) written as ∑ i, |x t i − x s i| ≤ L |t − s|, and u.o.c. convergence as uniform convergence for the sup-norm uniformity; reason: the ℓ¹ and sup norms are equivalent on ℝ^d, so uniform convergence on [0, t] is the same notion
--   - encoding: sup over x ∈ A of |x(t) − x(s)| ≤ L|t − s| → the bound for each x ∈ A; reason: equivalent
--   - encoding: y ∈ C^d → Continuous y (membership in D^d is part of ConvergesUOC); reason: same paths
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.3, Corollary A.9, eq. (A.2), p.259 (PDF 275)

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC

open Filter Topology
open scoped NNReal

namespace ProcessingNetworks.PathCompact

/-- **Corollary A.9** (equi-Lipschitz paths starting at 0 have a u.o.c. convergent subsequence),
Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org), Appendix A,
§A.3, Corollary A.9, eq. (A.2), p.259 (PDF 275).

Fix an integer `d > 0`. Let `A ⊂ C^d` be a set of continuous paths `x : ℝ₊ → ℝ^d` with
(a) `x(0) = 0` for each `x ∈ A`, and (b) `A` equi-Lipschitz: there is `L > 0` with
`sup_{x ∈ A} |x(t) − x(s)| ≤ L |t − s|` for all `s, t ∈ ℝ₊` (A.2). Then every sequence
`{xₙ} ⊂ A` has a subsequence `{x_{n_k}}` with `x_{n_k} → y` u.o.c. for some `y ∈ C^d`.

**Formalization Note.** `ℝ^d` is `Fin d → ℝ` and `|·|` is written out as the `ℓ¹` norm
`∑ i, |v i|` (Guide, p.xv). The supremum over `A` in (A.2) is stated pointwise for each
`x ∈ A`, which is equivalent. A subsequence is `xs ∘ φ` with `φ` strictly increasing; u.o.c.
convergence is `ConvergesUOC` (Definition A.6), and `y ∈ C^d` is `Continuous y` (membership in
`D^d` is part of `ConvergesUOC`). -/
theorem corollary_A_9 (d : ℕ) (hd : 0 < d) (A : Set (ℝ≥0 → Fin d → ℝ))
    (hcont : ∀ x ∈ A, Continuous x) (hzero : ∀ x ∈ A, x 0 = 0)
    (hLip : ∃ L : ℝ, 0 < L ∧ ∀ x ∈ A, ∀ s t : ℝ≥0,
      ∑ i, |x t i - x s i| ≤ L * |(t : ℝ) - (s : ℝ)|)
    (xs : ℕ → ℝ≥0 → Fin d → ℝ) (hxs : ∀ n, xs n ∈ A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℝ≥0 → Fin d → ℝ, Continuous y ∧
      ConvergesUOC (fun k => xs (φ k)) y := by sorry

end ProcessingNetworks.PathCompact
