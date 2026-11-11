-- Prove2me | Theorems.Thm_TensorBeyond_Main_theorem_6_1
-- name    : TensorBeyond.Main.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:15.078576+00:00
-- url     : https://prove2.me/theorems/2ee3a6d8-0909-42d1-8ae1-d4c3da0b6569
-- title:
--   Theorem 6.1 — $n^{\tilde O(\ell)}$-time recovery of all components of a random order-4 tensor of rank $\tilde o(n^2\ell)$
-- statement:
--   Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes4}$ and $\langle x,y\rangle=\frac1nx^\top y$. For every $c>0$ there are $C,D>0$, $N_0$ and **one** program $P$ of the randomized real RAM such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le n^2\ell/(\log n)^C$:
--
--   - on input $(n,m,\ell,T)$, $P$ halts within $n^{D\ell(\log n)^D}$ steps for every sample and every random tape;
--   - with probability at least $1-(\log n)^{-c}$ over the sample and the tapes, the outputs $\hat v_1,\dots,\hat v_m$ satisfy $\langle\hat v_j,\hat v_j\rangle=1$ and, for some permutation $\pi$ of $[m]$,
--   $$|\langle\hat v_{\pi(i)},v_i\rangle|\ \ge\ 1-(\log n)^{-c}\qquad\text{for all } i\in[m].$$
--
--   This is the case $k=4$ of Theorem 1.1, under the standing assumption $n\le m$ of §4.
--
--   Differences from the source:
--   - reading: |⟨v̂_i, v_i⟩| ≥ 1 − õ(1) with π introduced and unused → |⟨v̂_{π(i)}, v_i⟩| ≥ 1 − (log n)^{−c}; reason: obvious typo, as in footnote 1 of Theorem 1.1; read literally the claim is impossible for m ≥ 2 by exchangeability
--   - reading: ℓ = õ(n), m = õ(n²ℓ), time n^{Õ(ℓ)}, õ(1), 1 − õ(1) → for every c there are C, D, N₀ with ℓ ≤ n/(log n)^C, m ≤ n²ℓ/(log n)^C, time n^{Dℓ(log n)^D}, accuracy and failure probability (log n)^{−c}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: "an algorithm" → one program P of the published randomized real RAM, chosen before n, m, ℓ, given n, m, ℓ and T, halting within the bound on every sample and tape; reason: the paper names no machine; a uniform algorithm with worst-case time
--   - reading: outputs v̂_i (normalization not restated) → ⟨v̂_j, v̂_j⟩ = 1 for every j; reason: the outputs are unit vectors (§2.1, [BKS15] rounding); without it scaling a weakly correlated vector meets the bound
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: ℓ is the SoS level (§5.1 takes ℓ ≥ 4); at ℓ = 0 the time bound would be one step
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m; reason: §4.1 "Throughout"; the polynomial bound is implied by m ≤ n³
--   - encoding: input "the entries of T", outputs v̂_i, probability over v and the algorithm's coins → memory layout (n, m, ℓ, entries of T in lexicographic order), outputs read from fixed cells, failure probability averaged over v of the tape law's outer measure; reason: Lean representation of the paper's input, output and randomness
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 31 (PDF 33), Theorem 6.1

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Machine
import Definitions.Def_TensorBeyond_Main_Model

set_option autoImplicit false

namespace TensorBeyond.Main

open KXorTPCA.Reduction

/-- Theorem 6.1 (`k = 4`): for every `c > 0` there are `C, D > 0`, `N₀` and one program `P` such
that for all `n ≥ N₀`, `ℓ ≥ 1` and `n ≤ m` with `ℓ ≤ n/(log n)^C` and `m ≤ n²ℓ/(log n)^C`: `P`
halts within `n^{D ℓ (log n)^D}` steps on every sample and tape, and with probability at least
`1 − (log n)^{−c}` there is a permutation `π` with `|⟨v̂_{π(i)}, v_i⟩| ≥ 1 − (log n)^{−c}` for all
`i`, the outputs being unit vectors. -/
theorem theorem_6_1 (c : ℝ) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∃ P : Program,
      ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
        (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
        (m : ℝ) ≤ (n : ℝ) ^ 2 * (ℓ : ℝ) / Real.log (n : ℝ) ^ C →
        (∀ (v : Sample n m) (ω : Tapes),
          HaltsWithin P (encode 4 n m ℓ v) ω ((n : ℝ) ^ (D * (ℓ : ℝ) * Real.log (n : ℝ) ^ D))) ∧
        failProb n m (fun v ω =>
            ¬ Recovers 4 (outVecs P 4 n m (encode 4 n m ℓ v) ω) v (Real.log (n : ℝ) ^ (-c))) ≤
          Real.log (n : ℝ) ^ (-c) := by sorry

end TensorBeyond.Main
