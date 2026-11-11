-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_6_2
-- name    : TensorBeyond.Main.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:09.420813+00:00
-- url     : https://prove2.me/theorems/eae3bab4-2dac-4ea5-ad86-6a63ce0bfb3a
-- title:
--   Lemma 6.2 — feasibility of $\mathcal P_\xi$ for $k=4$: $\langle T,v_i^{\otimes4}\rangle\ge1+\xi$ for every $i$
-- statement:
--   Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes4}$ and $\langle x,y\rangle=\frac1nx^\top y$. For every $c>0$ there are $C>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le n^2\ell/(\log n)^C$, with probability at least $1-(\log n)^{-c}$,
--   $$\langle T,v_i^{\otimes4}\rangle\ \ge\ 1+\xi\quad\text{for every } i\in[m],\qquad \xi=m\cdot\frac{n(3n-2)}{n^4}-(\log n)^{-c}\ \ \text{(6.1)}.$$
--   Every planted component is therefore a feasible point of the program $\mathcal P_\xi$.
--
--   Differences from the source:
--   - reading: ℓ = õ(n), m = õ(n²ℓ), "with high probability", the õ(1) of (6.1) → for every c there are C, N₀ with ℓ ≤ n/(log n)^C, m ≤ n²ℓ/(log n)^C, probability ≥ 1 − (log n)^{−c} and ξ = m n(3n−2)/n⁴ − (log n)^{−c}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: ℓ is the SoS level (§5.1 takes ℓ ≥ 4); ℓ = 0 makes the range empty
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m; reason: the polynomial bound is implied by m ≤ n²ℓ/(log n)^C ≤ n³
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 31 (PDF 33), Lemma 6.2 and Eq. (6.1)

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 6.2 (feasibility of `𝒫_ξ` for `k = 4`): for every `c > 0` there are `C > 0` and `N₀`
such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with `ℓ ≤ n/(log n)^C` and `m ≤ n²ℓ/(log n)^C`, with
probability at least `1 − (log n)^{−c}`, every component has
`⟨T, v_i^{⊗4}⟩ ≥ 1 + ξ`, `ξ = m n(3n−2)/n⁴ − (log n)^{−c}` (6.1). -/
theorem lemma_6_2 (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ (n : ℝ) ^ 2 * (ℓ : ℝ) / Real.log (n : ℝ) ^ C →
      1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        ∀ i : Fin m, 1 + xi4 n m (Real.log (n : ℝ) ^ (-c)) ≤ pairing 4 v (vec v i)) := by sorry

end TensorBeyond.Main
