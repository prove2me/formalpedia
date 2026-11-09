-- Prove2me | Theorems.Thm_ProxGapTight_supercode_prob
-- name    : ProxGapTight.supercode_prob
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:45:15.199202+00:00
-- url     : https://prove2.me/theorems/a3a3cf4c-716e-4f32-b2d1-979936751569
-- title:
--   Proof of Theorem 3.1, p.14 — random supercode: $\Pr[x\in C]\le 2q^{K-N}$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $C_0\subseteq\mathbb F_q^N$ a linear code, $k$ an integer with $\dim C_0\le k\le N$, and $x\notin C_0$. If $C$ is a uniformly random $k$-dimensional code with $C\supseteq C_0$, then
--   $$
--   \Pr[x\in C]=\frac{q^{k-\dim C_0}-1}{q^{N-\dim C_0}-1}\le 2q^{k-N}.
--   $$
--
--   In the proof $k=K=N-d_0+1-h$; the bound shows that enlarging $C_0$ at random to a near-MDS code keeps its minimum distance and keeps $f,g$ far, with positive probability.
--
--   **Formalization Note** The probability is the ratio of the number of $k$-dimensional supercodes containing $x$ to the number of all $k$-dimensional supercodes.
--
--   Differences from the source:
--   - generalization: K := N − d₀ + 1 − h → any k with dim C₀ ≤ k ≤ N; reason: the paper's K is one such k (it exceeds dim C₀ in the 'Otherwise' case)
--   - generalization: F_q → any finite field F, q = Fintype.card F; reason: the statement specializes to F_q
--   - encoding: Pr over a uniformly random K-dimensional supercode; '= 2q^{−d₀+1−h}' → ratio of Set.ncard; the last equality is not restated; reason: exact for the finite uniform law; the last equality only substitutes K = N − d₀ + 1 − h
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), proof of Theorem 3.1, p.14, display

import Mathlib

namespace ProxGapTight

/-- **Random supercode**, proof of Theorem 3.1, Kominers, Thaler, Zheng, manuscript (Sept. 2026),
p.14, display: for a uniformly random `K`-dimensional supercode `C ⊇ C₀` and any fixed `x ∉ C₀`,
`Pr[x ∈ C] = (q^{K−dim C₀} − 1)/(q^{N−dim C₀} − 1) ≤ 2q^{K−N}`.

**Formalization Note.** `F_q` is any finite field `F`, `q = |F|`; the dimension (the paper's `K`)
is written `k`, any value with `dim C₀ ≤ k ≤ N` (the paper's `K = N − d₀ + 1 − h` is one). The
uniform law on the finite set of `k`-dimensional supercodes makes the probability a ratio of
`Set.ncard`s. Both the equality and the bound are stated; `q^{k−N}` is an integer power. -/
theorem supercode_prob (F : Type) [Field F] [Fintype F] (N k : ℕ)
    (C₀ : Submodule F (Fin N → F)) (hk₀ : Module.finrank F C₀ ≤ k) (hkN : k ≤ N)
    (x : Fin N → F) (hx : x ∉ C₀) :
    ((Set.ncard {C : Submodule F (Fin N → F) | Module.finrank F C = k ∧ C₀ ≤ C ∧ x ∈ C} : ℝ) /
        (Set.ncard {C : Submodule F (Fin N → F) | Module.finrank F C = k ∧ C₀ ≤ C} : ℝ) =
      ((Fintype.card F : ℝ) ^ (k - Module.finrank F C₀) - 1) /
        ((Fintype.card F : ℝ) ^ (N - Module.finrank F C₀) - 1)) ∧
    ((Fintype.card F : ℝ) ^ (k - Module.finrank F C₀) - 1) /
        ((Fintype.card F : ℝ) ^ (N - Module.finrank F C₀) - 1) ≤
      2 * (Fintype.card F : ℝ) ^ ((k : ℤ) - (N : ℤ)) := by sorry

end ProxGapTight
