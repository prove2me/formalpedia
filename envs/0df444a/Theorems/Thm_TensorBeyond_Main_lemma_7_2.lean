-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_7_2
-- name    : TensorBeyond.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:14:13.614092+00:00
-- url     : https://prove2.me/theorems/669cf851-1f19-4c5e-bfd1-4787079bb2a1
-- title:
--   Lemma 7.2 — feasibility of $\mathcal P_\xi$ for $k=3$: $\langle T,v_i^{\otimes3}\rangle\ge1+\xi$ for every $i$
-- statement:
--   Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes3}$ and $\langle x,y\rangle=\frac1nx^\top y$. For every $c>0$ there are $C>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le n^{3/2}\sqrt\ell/(\log n)^C$, with probability at least $1-(\log n)^{-c}$,
--   $$\langle T,v_i^{\otimes3}\rangle\ \ge\ 1+\xi\quad\text{for every } i\in[m],\qquad \xi=-(\log n)^{-c}\ \ \text{(7.1)}.$$
--   Every planted component is therefore a feasible point of the program $\mathcal P_\xi$ for $k=3$.
--
--   Differences from the source:
--   - reading: T = Σ_i v_i^{⊗4} and ⟨T, v_i^{⊗4}⟩ → T = Σ_i v_i^{⊗3} and ⟨T, v_i^{⊗3}⟩; reason: obvious typo, the title, (7.1) and the proof ("the diagonal term ⟨v_i, v_i⟩³ and the cross terms Σ_j⟨v_j, v_i⟩³") are about order 3; literally the claim is trivial
--   - reading: ℓ = õ(n), m = õ(n^{3/2}√ℓ), ξ = −õ(1), "with high probability" → for every c there are C, N₀ with ℓ ≤ n/(log n)^C, m ≤ n^{3/2}√ℓ/(log n)^C, ξ = −(log n)^{−c}, probability ≥ 1 − (log n)^{−c}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: ℓ is the SoS level (§5.1 takes ℓ ≥ 4); ℓ = 0 makes the range empty
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m; reason: the polynomial bound is implied by m ≤ n²
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 40 (PDF 42), Lemma 7.2 and Eq. (7.1)

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 7.2 (feasibility of `𝒫_ξ` for `k = 3`), with `T = ∑_i v_i^{⊗3}`: for every `c > 0`
there are `C > 0` and `N₀` such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with `ℓ ≤ n/(log n)^C` and
`m ≤ n^{3/2}√ℓ/(log n)^C`, with probability at least `1 − (log n)^{−c}`, every component has
`⟨T, v_i^{⊗3}⟩ ≥ 1 + ξ`, `ξ = −(log n)^{−c}` (7.1). -/
theorem lemma_7_2 (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (ℓ : ℝ) / Real.log (n : ℝ) ^ C →
      1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        ∀ i : Fin m, 1 + -Real.log (n : ℝ) ^ (-c) ≤ pairing 3 v (vec v i)) := by sorry

end TensorBeyond.Main
