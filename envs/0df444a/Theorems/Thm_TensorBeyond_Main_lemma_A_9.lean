-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_A_9
-- name    : TensorBeyond.Main.lemma_A_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:11.449544+00:00
-- url     : https://prove2.me/theorems/2f37c726-c24b-48cf-97b9-e7641348a11c
-- title:
--   Lemma A.9 — $\{x_u^2=1\}\vdash_6 h_6(x)\le O(\sqrt m\,n^6\log^9n)$
-- statement:
--   In this item $\langle\cdot,\cdot\rangle$ is the unnormalized dot product of Appendix A. Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$ and
--   $$h_6(x)=\sum_{i\ne j}(v_i^\top v_j)\,(v_i^\top x)^3\,(v_j^\top x)^3 .$$
--   For every $c>0$ there are $C,D>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le\sqrt{n^3\ell}/(\log n)^C$ (the model of Section 5.1 for $k=3$, the setting of Appendix A), with probability at least $1-(\log n)^{-c}$,
--   $$\{x_u^2=1\ \forall u\in[n]\}\ \vdash_6\ h_6(x)\ \le\ D\sqrt m\,n^6\log^9n .$$
--   It controls the noise term in the second Cauchy–Schwarz step of Lemma 7.16.
--
--   Differences from the source:
--   - encoding: ⟨v_i, v_j⟩, ⟨v_i, x⟩ → unnormalized v_iᵀv_j, v_iᵀx; reason: Appendix A's convention, under which the bound √m n⁶ is stated
--   - reading: O(·), "with high probability" → for every c there are D, N₀ with bound D√m n⁶ log⁹ n and probability ≥ 1 − (log n)^{−c}; reason: the paper's conventions, with "for every c" the stronger reading
--   - reading: no range of n, m stated → for every c there are C, N₀ with ℓ ≥ 1, ℓ ≤ n/(log n)^C, n ≤ m ≤ √(n³ℓ)/(log n)^C; reason: Appendix A ("Remaining Norm Bounds for the Odd Case") works in the k = 3 model of §5.1 (ℓ = õ(n), m = õ(n^{3/2}ℓ^{1/2})) with the standing n ≤ m of §4.1; without it the bound fails at x = v_1 once m ≫ n² (h_6(v_1) ≈ 9m²n³)
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 66 (PDF 68), Lemma A.9

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma A.9 (unnormalized dot product; Appendix A, the odd case `k = 3`): for every `c > 0`
there are `C, D > 0` and `N₀` such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with
`ℓ ≤ n/(log n)^C` and `m ≤ √(n³ℓ)/(log n)^C` (the model of Section 5.1 for `k = 3`), with
probability at least `1 − (log n)^{−c}`, `{x_u² = 1} ⊢_6 h_6(x) ≤ D √m n⁶ log⁹ n`. -/
theorem lemma_A_9 (c : ℝ) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 3 * (ℓ : ℝ)) / Real.log (n : ℝ) ^ C →
      1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        SoSProves 6 []
          (MvPolynomial.C (D * Real.sqrt (m : ℝ) * (n : ℝ) ^ 6 * Real.log (n : ℝ) ^ 9) -
            hNoise v 3)) := by sorry

end TensorBeyond.Main
