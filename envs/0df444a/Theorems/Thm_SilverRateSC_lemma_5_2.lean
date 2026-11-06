-- Prove2me | Theorems.Thm_SilverRateSC_lemma_5_2
-- name    : SilverRateSC.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:45:02.53532+00:00
-- url     : https://prove2.me/theorems/c91438d0-ae1f-483d-a836-ecd67315fd8d
-- title:
--   Lemma 5.2 — each stepsize index is considered by at most two repairs
-- statement:
--   Fix integers $n,m\ge1$, a nonnegative schedule $(h_1,\dots,h_n)$, $S_0>0$, and $B:=\lceil n/m\rceil$. Let repairs $j=1,\dots,J$, $J\le B$, consider the indices $u_j,\dots,v_j$, with last checkpoint $p_j\in\{u_j,\dots,v_j\}$, $1\le u_j$, $v_j\le n$, $u_{j+1}\ge p_j+1$, and $n_j:=v_j-u_j+1$. Suppose
--   $$\sum_{t=u_j}^{v_j}h_t\ge S_0,\qquad \sum_{t=p_j+1}^{v_j}h_t\le S_0/4\qquad(1\le j\le J).$$
--   Then each stepsize index belongs to at most two of the sets $\{u_j,\dots,v_j\}$; consequently
--   $$\sum_{j=1}^Jn_j\le2n,\qquad \sum_{j=1}^J\log(n_j+1)\le B\log(2m+1).$$
--
--   The count turns the per-repair loss $c_0(n_j+1)^{-4}$ of Lemma 4.2 into a total loss $\exp[-CB\log(m+1)]$.
--
--   Differences from the source:
--   - generalization: repairs produced by the checkpoint-selection procedure (at most one after each block, v_j the end of the current block) → every family (u_j, p_j, v_j)_{j ≤ J} with 1 ≤ u_j ≤ p_j ≤ v_j ≤ n, u_{j+1} ≥ p_j + 1, J ≤ ⌈n/m⌉ and (23); reason: the proof uses only these relations; every procedure-produced family satisfies them, so the statement specializes to the source's
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the paper pairs log with exp; another base changes only the constants
--   - encoding: h_t, (u_j, p_j, v_j), n_j = v_j − u_j + 1, B = ⌈n/m⌉, belonging to at most two sets → h : ℕ → ℝ and u p v : ℕ → ℕ read at 1-based positions, ℕ subtraction v j − u j + 1, ⌈(n:ℝ)/m⌉₊, card of the filter of Finset.Icc 1 J at most 2 for every t; reason: same data; the subtraction is exact since u_j ≤ v_j, and an index t outside 1, …, n lies in no set
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 5.2, p.20; setting and (23), p.20

import Mathlib

namespace SilverRateSC

/-- **Lemma 5.2 (Counting stepsize indices considered by repairs).** Fix integers `n, m ≥ 1`, a
nonnegative schedule `(h_1, …, h_n)`, and `S_0 > 0`; let `B := ⌈n/m⌉`. Repairs `j = 1, …, J`,
`J ≤ B`, consider the stepsize indices `u_j, …, v_j` with last checkpoint `p_j ∈ {u_j, …, v_j}`,
`1 ≤ u_j`, `v_j ≤ n`, `u_{j+1} ≥ p_j + 1` (`1 ≤ j < J`), and `n_j := v_j − u_j + 1`. Suppose
`∑_{t=u_j}^{v_j} h_t ≥ S_0` and `∑_{t=p_j+1}^{v_j} h_t ≤ S_0/4` (`1 ≤ j ≤ J`) (23). Then each stepsize
index belongs to at most two of the sets `{u_j, …, v_j}`. Consequently,
`∑_{j=1}^J n_j ≤ 2n` and `∑_{j=1}^J log(n_j + 1) ≤ B log(2m + 1)`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 5.2, p. 20 (setting and (23), p. 20).

**Formalization Note** The lemma is stated for every family `(u_j, p_j, v_j)_{j ≤ J}` satisfying
the listed index relations and (23), not only for those produced by the checkpoint-selection
procedure (whose further properties, e.g. that `v_j` ends a block, are not used). `log` is the
natural logarithm; `B = ⌈n/m⌉₊`. -/
theorem lemma_5_2 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (h : ℕ → ℝ)
    (hh : ∀ t ∈ Finset.Icc 1 n, 0 ≤ h t) (S₀ : ℝ) (hS₀ : 0 < S₀) (J : ℕ)
    (hJ : J ≤ ⌈(n : ℝ) / m⌉₊) (u p v : ℕ → ℕ)
    (huv : ∀ j ∈ Finset.Icc 1 J, 1 ≤ u j ∧ u j ≤ p j ∧ p j ≤ v j ∧ v j ≤ n)
    (hup : ∀ j ∈ Finset.Icc 1 J, j < J → p j + 1 ≤ u (j + 1))
    (h23 : ∀ j ∈ Finset.Icc 1 J,
      S₀ ≤ ∑ t ∈ Finset.Icc (u j) (v j), h t ∧ ∑ t ∈ Finset.Icc (p j + 1) (v j), h t ≤ S₀ / 4) :
    (∀ t : ℕ, ((Finset.Icc 1 J).filter (fun j => u j ≤ t ∧ t ≤ v j)).card ≤ 2) ∧
      ∑ j ∈ Finset.Icc 1 J, (v j - u j + 1) ≤ 2 * n ∧
      ∑ j ∈ Finset.Icc 1 J, Real.log (((v j - u j + 1 : ℕ) : ℝ) + 1) ≤
        (⌈(n : ℝ) / m⌉₊ : ℝ) * Real.log (2 * m + 1) := by sorry

end SilverRateSC
