-- Prove2me | Theorems.Thm_SparseDisc_lemma_2_1
-- name    : SparseDisc.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:54:12.669251+00:00
-- url     : https://prove2.me/theorems/ac4dfcbe-1ab0-4844-a0f7-b2b394343bfe
-- title:
--   Lemma 2.1 — families of 1-Lipschitz set functions are odd 2-Lipschitz instances
-- statement:
--   Let $\iota$ be a finite set of items.
--
--   1. If $f : 2^{\iota} \to \mathbb R$ is 1-Lipschitz, then its imbalance function $g_f(x) = f(\{j : x_j = 1\}) - f(\{j : x_j = -1\})$ is odd and 2-Lipschitz, and it depends only on the coordinates in $R(f)$.
--   2. If $g : \{\pm1\}^{\iota} \to \mathbb R$ is odd and 2-Lipschitz, then $f(S) = \tfrac12 g(1_S - 1_{\iota \setminus S})$ is 1-Lipschitz, $g_f = g$, and $R(f)$ is the set of coordinates relevant to $g$.
--   3. For every family $F = (f_v)_{v \in V}$ of set functions,
--   $$
--   \operatorname{disc}(F) = \min_{x \in \{\pm1\}^{\iota}} \max_v |g_{f_v}(x)| .
--   $$
--
--   The lemma translates the discrepancy of set functions into the language of odd 2-Lipschitz functions on the cube, in which every upper bound of the paper is proved.
--
--   **Formalization Note** Part 3 is stated as: for every real $c$, $\operatorname{disc}(F) \le c$ iff some $x$ has $|g_{f_v}(x)| \le c$ for all $v$ (both minima are attained).
--
--   Differences from the source:
--   - encoding: the item set [m] → a finite type of items; reason: Lean convention; [m] is the case Fin m, and every finite set is in bijection with some [m]
--   - encoding: disc(F) = min_x max_i |g_{f_i}(x)| → for every real c: disc(F) ≤ c iff some x has |g_{f_v}(x)| ≤ c for all v; reason: both minima are over finite sets and attained, so equality of the minima is equivalent to agreement of all their sublevel statements
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Lemma 2.1, p.11

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_relevant
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_imbalance
import Definitions.Def_SparseDisc_signVec
import Definitions.Def_SparseDisc_relevantCoords
import Definitions.Def_SparseDisc_IsLip
import Definitions.Def_SparseDisc_IsOdd

namespace SparseDisc

/-- **Lemma 2.1** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), p.11). (a) If `f` is 1-Lipschitz, then `g_f` is odd
and 2-Lipschitz and depends only on the coordinates in `R(f)`. (b) If `g` is odd and 2-Lipschitz,
then `f(S) = ½ g(1_S − 1_{ι∖S})` is 1-Lipschitz, `g_f = g`, and `R(f)` is the set of coordinates
relevant to `g`. (c) For every family `F`, `disc(F) = min_x max_i |g_{f_i}(x)|`.

**Formalization Note** (c) is stated as `disc(F) ≤ c ↔ min_x max_i |g_{f_i}(x)| ≤ c` for every real
`c` (both minima are over finite sets and attained). -/
theorem lemma_2_1 :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Finset ι → ℝ), IsOneLipschitz f →
      IsOdd (imbalance f) ∧ IsLip 2 (imbalance f) ∧
        ∀ x y : Cube ι, (∀ j ∈ relevant f, x j = y j) → imbalance f x = imbalance f y) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → ℝ), IsOdd g → IsLip 2 g →
      IsOneLipschitz (fun S => g (signVec S) / 2) ∧
        imbalance (fun S => g (signVec S) / 2) = g ∧
        relevant (fun S => g (signVec S) / 2) = relevantCoords g) ∧
    (∀ (V ι : Type) [Fintype ι] [DecidableEq ι] (F : V → Finset ι → ℝ) (c : ℝ),
      DiscLE F c ↔ ∃ x : Cube ι, ∀ v, |imbalance (F v) x| ≤ c) := by sorry

end SparseDisc
