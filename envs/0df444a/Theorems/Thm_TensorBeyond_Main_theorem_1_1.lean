-- Prove2me | Theorems.Thm_TensorBeyond_Main_theorem_1_1
-- name    : TensorBeyond.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:20.616966+00:00
-- url     : https://prove2.me/theorems/4307fdd1-ec8d-4669-b65e-055922e797c1
-- title:
--   Theorem 1.1 — $n^{\tilde O(\ell)}$-time decomposition of random order-$k$ Rademacher tensors of rank $\tilde o(n^{k/2}\ell^{k/2-1})$, $k\in\{3,4\}$
-- statement:
--   Let $k\in\{3,4\}$, let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_{i=1}^mv_i^{\otimes k}$, and $\langle x,y\rangle=\frac1nx^\top y$. For every $c>0$ there are $C,D>0$, $N_0$ and **one** program $P$ of the randomized real RAM such that for all $n\ge N_0$, $\ell\ge1$ and $m$ with
--   $$\ell\le\frac{n}{(\log n)^C},\qquad m\le\frac{n^{k/2}\,\ell^{k/2-1}}{(\log n)^C},$$
--   - on input $(n,m,\ell,T)$, $P$ halts within $n^{D\ell(\log n)^D}$ steps for every sample and every random tape;
--   - with probability at least $1-(\log n)^{-c}$ over the sample and the tapes, the outputs $\hat v_1,\dots,\hat v_m\in\mathbb R^n$ satisfy $\langle\hat v_j,\hat v_j\rangle=1$ for every $j$, and for some permutation $\pi$ of $[m]$
--   $$\langle\hat v_{\pi(i)},v_i\rangle\ \ge\ 1-(\log n)^{-c}\ \ (k=3),\qquad |\langle\hat v_{\pi(i)},v_i\rangle|\ \ge\ 1-(\log n)^{-c}\ \ (k=4),\qquad\text{for all } i\in[m].$$
--
--   Polynomial-time algorithms decompose such tensors up to the spectral threshold $m\approx n^{k/2}$; this result trades running time $n^{\tilde O(\ell)}$ for rank $n^{k/2}\ell^{k/2-1}$, interpolating towards the information-theoretic threshold $n^{k-1}$ as $\ell$ grows to $n$.
--
--   Differences from the source:
--   - reading: ℓ = õ(n), m = õ(n^{k/2}ℓ^{k/2−1}), time n^{Õ(ℓ)}, õ(1) → for every c there are C, D, N₀ with ℓ ≤ n/(log n)^C, m ≤ n^{k/2}ℓ^{k/2−1}/(log n)^C, time n^{Dℓ(log n)^D}, accuracy (log n)^{−c}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: "with high probability" → failure probability ≤ (log n)^{−c}; reason: 1 − õ(1), as Theorem 6.1 restates it
--   - reading: "an algorithm" → one program P of the published randomized real RAM, chosen after k and c and before n, m, ℓ, given n, m, ℓ and T, halting within the bound on every sample and tape; reason: the paper names no machine; a uniform algorithm with worst-case time
--   - reading: ⟨v̂_i, v_i⟩ ≥ 1 − õ(1) for all i, with footnote 1 → ∃ π with ⟨v̂_{π(i)}, v_i⟩ ≥ 1 − (log n)^{−c} (|·| for even k); reason: footnote 1 is the precise guarantee
--   - reading: outputs v̂_i (normalization not restated) → ⟨v̂_j, v̂_j⟩ = 1 for every j; reason: the outputs are unit vectors (§2.1, [BKS15] rounding); without it scaling a weakly correlated vector meets the bound
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: ℓ is the SoS level (§5.1 takes ℓ ≥ 4); at ℓ = 0 the time bound would be one step
--   - encoding: input "the entries of T", outputs v̂_i, probability over v and the algorithm's coins → memory layout (n, m, ℓ, entries of T in lexicographic order), outputs read from fixed cells, failure probability averaged over v of the tape law's outer measure; reason: Lean representation of the paper's input, output and randomness
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 2 (PDF 4), Theorem 1.1 with footnote 1

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Machine
import Definitions.Def_TensorBeyond_Main_Model

set_option autoImplicit false

namespace TensorBeyond.Main

open KXorTPCA.Reduction

/-- Theorem 1.1 with footnote 1, for `k ∈ {3, 4}`: for every `c > 0` there are `C, D > 0`, `N₀`
and one program `P` such that for all `n ≥ N₀`, `ℓ ≥ 1` and `m` with `ℓ ≤ n/(log n)^C` and
`m ≤ n^{k/2} ℓ^{k/2−1}/(log n)^C`: `P` halts within `n^{D ℓ (log n)^D}` steps on every sample and
tape, and with failure probability at most `(log n)^{−c}` it outputs unit vectors `v̂_j` with
`⟨v̂_{π(i)}, v_i⟩ ≥ 1 − (log n)^{−c}` for some permutation `π` (absolute value for `k = 4`). -/
theorem theorem_1_1 (k : ℕ) (hk : k = 3 ∨ k = 4) (c : ℝ) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∃ P : Program,
      ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ →
        (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
        (m : ℝ) ≤ (n : ℝ) ^ ((k : ℝ) / 2) * (ℓ : ℝ) ^ ((k : ℝ) / 2 - 1) / Real.log (n : ℝ) ^ C →
        (∀ (v : Sample n m) (ω : Tapes),
          HaltsWithin P (encode k n m ℓ v) ω ((n : ℝ) ^ (D * (ℓ : ℝ) * Real.log (n : ℝ) ^ D))) ∧
        failProb n m (fun v ω =>
            ¬ Recovers k (outVecs P k n m (encode k n m ℓ v) ω) v (Real.log (n : ℝ) ^ (-c))) ≤
          Real.log (n : ℝ) ^ (-c) := by sorry

end TensorBeyond.Main
