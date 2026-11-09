-- Prove2me | Theorems.Thm_PerturbedWF_lemma_A_1
-- name    : PerturbedWF.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:29:24.75368+00:00
-- url     : https://prove2.me/theorems/1d8823e0-de8c-4159-ab39-8818713c4fd9
-- title:
--   Lemma A.1: a tree code over $\Sigma=\mathbb Z/145\mathbb Z$ (Schulman)
-- statement:
--   Let $\Sigma=\{0,1,\dots,q-1\}$ with $q=145$. For every $N>0$ there is a map $\varphi:\{0,1\}^{\le N}\to\Sigma^{\le N}$ converting every binary string into a sequence of labels of the same length (one label per bit) such that
--   1. the output label at position $t$ depends only on the first $t$ input bits;
--   2. if $x,y\in\{0,1\}^k$ and the first bit in which they differ is at position $k-t+1$, then $\varphi(x)$ and $\varphi(y)$ disagree in at least $t/2$ labels among the last $t$ positions.
--
--   This is the labelling that makes sibling edges of a general HST distinguishable in Theorem 3.4.
--
--   **Formalization Note.** $\Sigma$ is `ZMod 145`, a bit is a `Bool`, and $\varphi$ is a family $\varphi_k:\{0,1\}^k\to\Sigma^k$ ($k\le N$). Positions are 0-based in Lean (the paper's position $t$ is index $t-1$). Property 1 compares strings of possibly different lengths $k,k'\le N$; property 2 is $t\le2\cdot\#\{p\ge k-t:\varphi_k(x)_p\ne\varphi_k(y)_p\}$ for $1\le t\le k$.
--
--   Differences from the source:
--   - encoding: positions 1, …, k; the first difference at position k − t + 1; the last t positions → 0-based indices; the first difference at index k − t; indices k − t, …, k − 1; reason: index shift only; checked at t = 1 and t = k
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma A.1, p.30 (PDF p.31)

import Mathlib

namespace PerturbedWF

/-- **Lemma A.1** (p.30, PDF p.31), "due to [Sch96]". C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

Consider the space of labels `Σ = {0, 1, …, q − 1}` for `q = 145`. For any `N > 0` there is a
map `φ : {0, 1}^{≤N} → Σ^{≤N}` converting any binary string into a sequence of labels of the same
length (one label per bit) such that
1. the output label at position `t` depends only on the first `t` input bits;
2. if `x, y ∈ {0, 1}^k` and the first bit that differs is at position `k − t + 1`, then `φ(x)`
   and `φ(y)` disagree in at least `t/2` labels of the last `t` positions.

**Formalization Note.** `Σ = ZMod 145`, a bit is a `Bool`, and `φ` is a family
`φ k : (Fin k → Bool) → (Fin k → ZMod 145)` (strings of length `k`, used for `k ≤ N`). Positions are
0-based: the paper's position `t` is index `t − 1`. (1) says: for `k, k' ≤ N`, the label at index
`t` of a length-`k` and of a length-`k'` string agree whenever the two strings agree at the
indices `0, …, t`. (2) says: for `1 ≤ t ≤ k ≤ N`, if `x, y` agree at the indices `< k − t` and
differ at index `k − t`, then `t ≤ 2 · #{p : k − t ≤ p, φ k x p ≠ φ k y p}`. -/
theorem lemma_A_1 (N : ℕ) (hN : 0 < N) :
    ∃ φ : (k : ℕ) → (Fin k → Bool) → (Fin k → ZMod 145),
      (∀ k k', k ≤ N → k' ≤ N → ∀ (x : Fin k → Bool) (x' : Fin k' → Bool) (t : ℕ)
          (ht : t < k) (ht' : t < k'),
          (∀ p (hp : p ≤ t), x ⟨p, lt_of_le_of_lt hp ht⟩ = x' ⟨p, lt_of_le_of_lt hp ht'⟩) →
          φ k x ⟨t, ht⟩ = φ k' x' ⟨t, ht'⟩) ∧
      (∀ k, k ≤ N → ∀ x y : Fin k → Bool, ∀ t (ht1 : 1 ≤ t) (htk : t ≤ k),
          (∀ p : Fin k, p.1 < k - t → x p = y p) →
          x ⟨k - t, by omega⟩ ≠ y ⟨k - t, by omega⟩ →
          (t : ℝ) ≤ 2 * ((Finset.univ.filter
            (fun p : Fin k => k - t ≤ p.1 ∧ φ k x p ≠ φ k y p)).card : ℝ)) := by sorry

end PerturbedWF
