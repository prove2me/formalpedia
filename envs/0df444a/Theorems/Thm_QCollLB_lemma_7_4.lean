-- Prove2me | Theorems.Thm_QCollLB_lemma_7_4
-- name    : QCollLB.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:12.6152+00:00
-- url     : https://prove2.me/theorems/58ee2918-0b0d-435c-b9b7-6d6eda974cd7
-- title:
--   Lemma 7.4 — one-round success under the balanced distribution
-- statement:
--   Let $k\ge2$ be fixed. There is $C_k$ such that for all $N$, $q\ge N$, every injection $\iota:[N]\hookrightarrow\mathbb Z_q$, every public bucket map with buckets of size $k$ on $[n]$, $n=kN$, and every $t$ with $t+k+3\le n/8$, the average success probability of every one-round $t$-query algorithm for Promised $k$-to-one Finding on the balanced input $x^\pi$, $\pi$ uniform in $S_n$, satisfies
--   $$
--   p_{\mathrm{succ}}=\frac1{n!}\sum_{\pi\in S_n}\Pr[\text{success on }x^\pi]\le C_k\Big(\frac{t^k}{n^{k-1}}+\frac{t+1}n\Big).
--   $$
--
--   Differences from the source:
--   - encoding: average over uniform π → (1/n!) Σ_π; reason: definition of the average
--   - encoding: fixed public buckets and a fixed injection ι → every bucket map b from Fin (kN) to Fin N with fibres of size k and every injection ι from Fin N into ZMod q; reason: quantifying over all choices includes the fixed one; C_k is chosen before them
--   - encoding: output a set ρ of k indices; final PVM on A → an ordered k-tuple with distinct entries; computational-basis measurement followed by an arbitrary map out; reason: with arbitrary U_1 and workspace every PVM is diagonal in a rotated computational basis; injective k-tuples are k-sets
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Lemma 7.4, Eq. (76), p.55

import Mathlib
import Definitions.Def_QCollLB_OneRound
import Definitions.Def_QCollLB_Buckets

namespace QCollLB

/-- **Lemma 7.4 (One-round success under the balanced distribution)** (Peng–Wu, arXiv:2611.01767
(PDF sha256 4e5aba34…d9fc), Lemma 7.4, Eq. (76), p.55). Let `k ≥ 2` be fixed, `n = kN` and `q ≥ N`.
Use the public buckets and the balanced hard input `x^π_i = ι(b(π(i)))` for uniform `π ∈ S_n`. If
`t + k + 3 ≤ n/8`, the average success probability `p_succ` of every `t`-query one-round algorithm for
Promised `k`-to-one Finding satisfies `p_succ ≤ C_k (t^k/n^{k−1} + (t + 1)/n)`.

**Formalization Note.** `C_k` depends only on `k` and is chosen before `N, q, ι, b, t` and the
algorithm. The average over uniform `π` is `(1/n!) Σ_π`; by Claim 6.3 it equals the average over the
balanced distribution. The algorithm (any workspace size) and the success probability are those of
`OneRoundAlg` / `oneRoundSuccess`. -/
theorem lemma_7_4 (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, ∀ (N q : ℕ) [NeZero q], N ≤ q →
      ∀ (ι : Fin N ↪ ZMod q) (b : Fin (k * N) → Fin N), IsBucketMap k b →
      ∀ t : ℕ, ((t : ℝ) + k + 3 ≤ ((k * N : ℕ) : ℝ) / 8) →
      ∀ (w : ℕ) (A : OneRoundAlg (k * N) q t w)
        (out : ((Fin t → Fin (k * N)) × (Fin t → ZMod q)) × Fin w → (Fin 1 → Fin k → Fin (k * N))),
        (1 / ((k * N).factorial : ℝ)) *
            ∑ π : Equiv.Perm (Fin (k * N)), oneRoundSuccess A out (xPi ι b π) ≤
          C * ((t : ℝ) ^ k / ((k * N : ℕ) : ℝ) ^ (k - 1) + ((t : ℝ) + 1) / ((k * N : ℕ) : ℝ)) := by sorry

end QCollLB
