-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_5_1
-- name    : TensorBeyond.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:22.795648+00:00
-- url     : https://prove2.me/theorems/f126ffed-6423-4b66-bc47-fe2f02207367
-- title:
--   Lemma 5.1 — found vectors stay nearly orthogonal to the remaining components: $\langle v_i,\hat v_j\rangle^2\le0.01$
-- statement:
--   Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$ and $\langle x,y\rangle=\frac1n x^\top y$. For every $a>0$ and $c>0$ there are $C>0$ and $N_0$ such that for all $n\ge N_0$ and $n\le m\le n^a$, with probability at least $1-(\log n)^{-c}$ the following holds simultaneously for every $s<m$ and all vectors $\hat v_1,\dots,\hat v_s\in\mathbb R^n$ with $\langle\hat v_j,\hat v_j\rangle\le1$ and $|\langle\hat v_j,v_j\rangle|\ge1-(\log n)^{-C}$ ($j\le s$):
--   $$\langle v_i,\hat v_j\rangle^2\le0.01\qquad\text{for all } i>s,\ j\le s .$$
--   In the algorithm this keeps the semidefinite program feasible after the near-orthogonality constraints for the vectors found so far are added.
--
--   Differences from the source:
--   - generalization: v ∈ S found by the algorithm (the proof takes v ∈ {±1}^n) → every v̂_j ∈ ℝ^n with ⟨v̂_j, v̂_j⟩ ≤ 1; reason: covers the paper's unit and sign vectors, and the norm bound rules out scaling
--   - reading: "with high probability", õ(1) → for every c there are C, N₀ with probability ≥ 1 − (log n)^{−c} and |⟨v̂_j, v_j⟩| ≥ 1 − (log n)^{−C}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: one set S → the event holds simultaneously for every s < m and every v̂_1..v̂_s; reason: S is built by the algorithm from the sample, so the bound must be uniform in S
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m ≤ n^a for an arbitrary a > 0, constants depending on a; reason: §4.1 "Throughout, n ≤ m ≤ poly(n)"
--   - encoding: indices i > s, j ≤ s (1-based) → Fin m with i ≥ s, j < s (0-based); reason: Lean convention, same instances
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 30 (PDF 32), Lemma 5.1

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 5.1: for every `a > 0` and `c > 0` there are `C > 0` and `N₀` such that for all
`n ≥ N₀` and `n ≤ m ≤ n^a`, with probability at least `1 − (log n)^{−c}` over the sample, for
every `s < m` and all vectors `v̂_0, …, v̂_{s−1}` with `⟨v̂_j, v̂_j⟩ ≤ 1` and
`|⟨v̂_j, v_j⟩| ≥ 1 − (log n)^{−C}`, every later component `v_i` (`i ≥ s`) has
`⟨v_i, v̂_j⟩² ≤ 0.01` for all `j < s`. -/
theorem lemma_5_1 (a : ℝ) (ha : 0 < a) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n m : ℕ, N₀ ≤ n → n ≤ m → (m : ℝ) ≤ (n : ℝ) ^ a →
      1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        ∀ s : ℕ, s < m → ∀ vhat : Fin m → Fin n → ℝ,
          (∀ j : Fin m, (j : ℕ) < s →
            ip (vhat j) (vhat j) ≤ 1 ∧ 1 - Real.log (n : ℝ) ^ (-C) ≤ |ip (vhat j) (vec v j)|) →
          ∀ i j : Fin m, s ≤ (i : ℕ) → (j : ℕ) < s →
            ip (vec v i) (vhat j) ^ 2 ≤ (1 / 100 : ℝ)) := by sorry

end TensorBeyond.Main
