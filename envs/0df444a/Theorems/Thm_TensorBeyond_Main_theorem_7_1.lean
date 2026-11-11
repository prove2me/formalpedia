-- Prove2me | Theorems.Thm_TensorBeyond_Main_theorem_7_1
-- name    : TensorBeyond.Main.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:09.627892+00:00
-- url     : https://prove2.me/theorems/7edb1e97-1e49-477a-b20c-5f7e86e6ea62
-- title:
--   Theorem 7.1 — $n^{\tilde O(\ell)}$-time recovery of all components of a random order-3 tensor to error $\sqrt{\varepsilon n}$ (as printed)
-- statement:
--   In this item distances are Euclidean, $\|x\|_2=\sqrt{x^\top x}$ (the convention of Section 7). Let $v_1,\dots,v_m\in\{\pm1\}^n$ and $T=\sum_iv_i^{\otimes3}$. For every $\varepsilon\in(0,1)$ there are $C,D>0$, $N_0$ and **one** program $P$ of the randomized real RAM such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le\sqrt{n^3\ell}/(\log n)^C$, for **every** sample $v$ and every random tape, $P$ on input $(n,m,\ell,T)$ halts within $n^{D\ell(\log n)^D}$ steps and outputs $\hat v_1,\dots,\hat v_m$ with
--   $$\|\hat v_{\pi(i)}-v_i\|_2\ \le\ \sqrt{\varepsilon n}\qquad\text{for all } i\in[m]$$
--   for some permutation $\pi$ of $[m]$.
--
--   This is the case $k=3$ of the main result, stated as printed: the paper gives no success probability, so the guarantee is claimed for every realization (a finding about this is recorded separately).
--
--   Differences from the source:
--   - reading: ℓ ≤ n/poly log n, m ≤ √(n³ℓ)/poly log n, time n^{Õ(ℓ)} → there are C, D, N₀ with ℓ ≤ n/(log n)^C, m ≤ √(n³ℓ)/(log n)^C, time n^{Dℓ(log n)^D}; reason: the paper's conventions (p. 2), constants fixed before n, m, ℓ
--   - reading: "an algorithm" → one program P of the published randomized real RAM, chosen after ε and before n, m, ℓ, given n, m, ℓ and T, halting within the bound on every sample and tape; reason: the paper names no machine; a uniform algorithm with worst-case time
--   - encoding: "approximate the components of T with error at most √(εn), up to a permutation" → ∃ π, ‖v̂_{π(i)} − v_i‖₂ ≤ √(εn) for all i (Euclidean, unnormalized); reason: §7's convention, under which the error √(εn) is stated
--   - encoding: input T, outputs v̂_i → memory layout (n, m, ℓ, entries of T in lexicographic order), outputs read from fixed cells; reason: Lean representation of the paper's input and output
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 40 (PDF 42), Theorem 7.1

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Machine
import Definitions.Def_TensorBeyond_Main_Model

set_option autoImplicit false

namespace TensorBeyond.Main

open KXorTPCA.Reduction

/-- Theorem 7.1, as printed (no success probability): for every `ε ∈ (0, 1)` there are
`C, D > 0`, `N₀` and one program `P` such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with
`ℓ ≤ n/(log n)^C` and `m ≤ √(n³ℓ)/(log n)^C`, on every sample of `k = 3` components and every tape,
`P` halts within `n^{D ℓ (log n)^D}` steps and its outputs satisfy
`‖v̂_{π(i)} − v_i‖₂ ≤ √(εn)` for all `i`, for some permutation `π`. -/
theorem theorem_7_1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∃ P : Program,
      ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
        (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
        (m : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 3 * (ℓ : ℝ)) / Real.log (n : ℝ) ^ C →
        ∀ (v : Sample n m) (ω : Tapes),
          HaltsWithin P (encode 3 n m ℓ v) ω ((n : ℝ) ^ (D * (ℓ : ℝ) * Real.log (n : ℝ) ^ D)) ∧
          ∃ π : Equiv.Perm (Fin m), ∀ i : Fin m,
            Real.sqrt (∑ u : Fin n,
                (outVecs P 3 n m (encode 3 n m ℓ v) ω (π i) u - vec v i u) ^ 2) ≤
              Real.sqrt (ε * (n : ℝ)) := by sorry

end TensorBeyond.Main
