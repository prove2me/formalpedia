-- Prove2me | Theorems.Thm_ProcessingNetworks_PathCompact_lemma_A_11
-- name    : ProcessingNetworks.PathCompact.lemma_A_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:00.720976+00:00
-- url     : https://prove2.me/theorems/75c6198d-137d-4c6f-8083-8ba2bd99344e
-- title:
--   Lemma A.11 — increment-dominated monotone paths have a u.o.c. convergent subsequence with continuous limit
-- statement:
--   For each $n\in\mathbb N$ let $f_n,g_n\in D(\mathbb R_+,\mathbb R)$ be nondecreasing with $f_n(0)=g_n(0)=0$, and suppose each pair is increment-dominated:
--
--   $$f_n(t)-f_n(s)\le g_n(t)-g_n(s),\qquad0\le s\le t.\tag{A.7}$$
--
--   Assume $g_n\to g$ u.o.c. and $g$ is continuous. Then there exist a subsequence $\{n_k\}$ and a continuous function $f$ such that
--
--   $$f_{n_k}\to f\quad\text{u.o.c.}$$
--
--   The lemma is used in the proof of Theorem 11.4: nondecreasing paths whose increments are dominated by those of a u.o.c. convergent sequence with continuous limit have u.o.c. convergent subsequences, without any Lipschitz bound of their own.
--
--   Differences from the source:
--   - encoding: time set ℝ₊, index set ℕ = {1, 2, …}, a subsequence {n_k} → ℝ≥0, ℕ (from 0), a strictly increasing φ : ℕ → ℕ; reason: Lean convention; same instances
--   - encoding: D (right continuous on ℝ₊ with left limits on (0, ∞)) and C (continuous functions) → the public predicate RBMSensitivity.IsRCLL and Continuous; reason: IsRCLL asks right continuity at every t and a left limit at every t, the latter being automatic at t = 0 where the left filter is trivial; same paths
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.3, Lemma A.11, eq. (A.7), p.261 (PDF 277)

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC

open Filter Topology
open scoped NNReal

namespace ProcessingNetworks.PathCompact

/-- **Lemma A.11** (increment-dominated monotone paths have a u.o.c. convergent subsequence),
Dai & Harrison, *Processing Networks* (pre-publication draft 2020-4-2, spnbook.org), Appendix A,
§A.3, Lemma A.11, eq. (A.7), p.261 (PDF 277); used in the proof of Theorem 11.4.

Suppose that for each `n` the functions `fₙ, gₙ ∈ D(ℝ₊, ℝ)` are nondecreasing with
`fₙ(0) = gₙ(0) = 0`, and that `fₙ(t) − fₙ(s) ≤ gₙ(t) − gₙ(s)` for `0 ≤ s ≤ t` (A.7). Assume
that `gₙ → g` u.o.c. and `g` is continuous. Then there is a subsequence `{n_k}` such that
`f_{n_k} → f` u.o.c., where `f` is a continuous function.

**Formalization Note.** Time is `ℝ≥0` and the book's index set `{1, 2, …}` is `ℕ`.
`D(ℝ₊, ℝ)` is `RBMSensitivity.IsRCLL`, "nondecreasing" is `Monotone`, u.o.c. is
`ConvergesUOC` (Definition A.6, which also requires the limit to lie in `D`), and a
subsequence is `fs ∘ φ` with `φ` strictly increasing. -/
theorem lemma_A_11 (fs gs : ℕ → ℝ≥0 → ℝ)
    (hfD : ∀ n, RBMSensitivity.IsRCLL (fs n)) (hgD : ∀ n, RBMSensitivity.IsRCLL (gs n))
    (hfmono : ∀ n, Monotone (fs n)) (hgmono : ∀ n, Monotone (gs n))
    (hf0 : ∀ n, fs n 0 = 0) (hg0 : ∀ n, gs n 0 = 0)
    (hinc : ∀ n, ∀ s t : ℝ≥0, s ≤ t → fs n t - fs n s ≤ gs n t - gs n s)
    (g : ℝ≥0 → ℝ) (hgcont : Continuous g) (hconv : ConvergesUOC gs g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ≥0 → ℝ, Continuous f ∧
      ConvergesUOC (fun k => fs (φ k)) f := by sorry

end ProcessingNetworks.PathCompact
