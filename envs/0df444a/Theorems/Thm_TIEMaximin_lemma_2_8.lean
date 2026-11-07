-- Prove2me | Theorems.Thm_TIEMaximin_lemma_2_8
-- name    : TIEMaximin.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:25.238326+00:00
-- url     : https://prove2.me/theorems/c257ce9b-f9ba-477c-a155-50c14c884e60
-- title:
--   Lemma 2.8 — the rounded-prefix lemma
-- statement:
--   Let $v_1\ge\dots\ge v_m\ge0$, $0\le w_j\le1$ for each $j$, and $S\subseteq\{1,\dots,m\}$.
--
--   1. If $|S\cap\{1,\dots,t\}|\le\lceil\sum_{j=1}^t w_j\rceil$ for every $t=1,\dots,m$, then $\sum_{j\in S}v_j\le\sum_{j=1}^m w_jv_j+v_1$.
--   2. If $|S\cap\{1,\dots,t\}|\ge\lfloor\sum_{j=1}^t w_j\rfloor$ for every $t=1,\dots,m$, then $\sum_{j\in S}v_j\ge\sum_{j=1}^m w_jv_j-v_1$.
--
--   If all weights are multiples of $1/k$ for a positive integer $k$, the error $v_1$ in both statements can be replaced by $(1-1/k)v_1$.
--
--   The lemma turns prefix-count bounds into value bounds. It is used for the load of the dummy agents and for rounding.
--
--   Differences from the source:
--   - encoding: items 1, …, m with first value v_1 → `Fin m` with `0 < m`, v_1 = `v ⟨0, hm⟩`; reason: v_1 must exist; for m = 0 the statement has no v_1
--   - encoding: weights multiples of 1/k → w_j = c/k with c a natural number; reason: the weights are nonnegative; same instances
--   - encoding: v_1 ≥ ⋯ ≥ v_m ≥ 0 → `Antitone v` and `0 ≤ v j` for every j; reason: with v antitone, v_m ≥ 0 is equivalent to v_j ≥ 0 for all j
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 2.8, p.9

import Mathlib

namespace TIEMaximin

open Finset

/-- **Lemma 2.8, the rounded-prefix lemma** (p.9). Let `v_1 ≥ ⋯ ≥ v_m ≥ 0`, `0 ≤ w_j ≤ 1`, and `S ⊆
{1, …, m}`. (1) If `|S ∩ {1..t}| ≤ ⌈Σ_{j≤t} w_j⌉` for every `t = 1, …, m`, then `Σ_{j∈S} v_j ≤ Σ_j
w_j v_j + v_1`. (2) If `|S ∩ {1..t}| ≥ ⌊Σ_{j≤t} w_j⌋` for every `t`, then `Σ_{j∈S} v_j ≥ Σ_j w_j
v_j − v_1`. If all weights are multiples of `1/k` for a positive integer `k`, the error `v_1` can
be replaced by `(1 − 1/k) v_1`.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 2.8, p.9.

**Formalization Note.** Items are `Fin m`, 0-based, so `v_1` is `v ⟨0, hm⟩`; `0 < m` is needed for
`v_1` to exist. The prefix `{1, …, t}` is `{j | j.val < t}`. "Multiple of `1/k`" with `0 ≤ w_j` is
`w_j = c/k` for a natural number `c`. -/
theorem lemma_2_8 {m : ℕ} (hm : 0 < m) (v w : Fin m → ℝ) (hv : Antitone v) (hv0 : ∀ j, 0 ≤ v j)
    (hw : ∀ j, 0 ≤ w j ∧ w j ≤ 1) (S : Finset (Fin m)) :
    ((∀ t, 1 ≤ t → t ≤ m →
        ((#{j ∈ S | j.val < t} : ℕ) : ℤ) ≤ ⌈∑ j with j.val < t, w j⌉) →
      ∑ j ∈ S, v j ≤ ∑ j, w j * v j + v ⟨0, hm⟩) ∧
    ((∀ t, 1 ≤ t → t ≤ m →
        ⌊∑ j with j.val < t, w j⌋ ≤ ((#{j ∈ S | j.val < t} : ℕ) : ℤ)) →
      ∑ j, w j * v j - v ⟨0, hm⟩ ≤ ∑ j ∈ S, v j) ∧
    ∀ k : ℕ, 0 < k → (∀ j, ∃ c : ℕ, w j = (c : ℝ) / (k : ℝ)) →
      ((∀ t, 1 ≤ t → t ≤ m →
          ((#{j ∈ S | j.val < t} : ℕ) : ℤ) ≤ ⌈∑ j with j.val < t, w j⌉) →
        ∑ j ∈ S, v j ≤ ∑ j, w j * v j + (1 - 1 / (k : ℝ)) * v ⟨0, hm⟩) ∧
      ((∀ t, 1 ≤ t → t ≤ m →
          ⌊∑ j with j.val < t, w j⌋ ≤ ((#{j ∈ S | j.val < t} : ℕ) : ℤ)) →
        ∑ j, w j * v j - (1 - 1 / (k : ℝ)) * v ⟨0, hm⟩ ≤ ∑ j ∈ S, v j) := by sorry

end TIEMaximin
