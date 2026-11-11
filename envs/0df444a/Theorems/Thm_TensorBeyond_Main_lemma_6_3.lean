-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_6_3
-- name    : TensorBeyond.Main.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:19.538394+00:00
-- url     : https://prove2.me/theorems/4921657b-efd2-43c7-8b15-cc0bc1d0d18c
-- title:
--   Lemma 6.3 — under $\mathcal P_\xi$, $\sum_i\langle v_i,x\rangle^8\ge1-\tilde o(1)$ and $\sum_i\langle v_i,x\rangle^6\le1+\tilde o(1)$ in degree $O(\ell)$
-- statement:
--   Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes4}$, $\langle x,y\rangle=\frac1nx^\top y$, and $\mathcal P_\xi=\{\langle T,x^{\otimes4}\rangle\ge1+\xi,\ x_u^2=1\ \forall u\}$ with $\xi=m\,n(3n-2)/n^4-(\log n)^{-c_1}$ as in (6.1). For every $c>0$ there are $C,c_1,D>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le n^2\ell/(\log n)^C$, with probability at least $1-(\log n)^{-c}$,
--   $$\mathcal P_\xi\vdash_{D\ell}\ \sum_{i=1}^m\langle v_i,x\rangle^8\ \ge\ 1-(\log n)^{-c}\qquad\text{and}\qquad \mathcal P_\xi\vdash_{D\ell}\ \sum_{i=1}^m\langle v_i,x\rangle^6\ \le\ 1+(\log n)^{-c}.$$
--   These are the premises of Lemma 5.3 for $k=4$, $d=6$.
--
--   Differences from the source:
--   - reading: ℓ = õ(n), m = õ(n²ℓ), degree O(ℓ), õ(1), "with high probability" → for every c there are C, D, N₀ with ℓ ≤ n/(log n)^C, m ≤ n²ℓ/(log n)^C, degree D·ℓ, bounds 1 ∓ (log n)^{−c}, probability ≥ 1 − (log n)^{−c}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: "ξ as in Equation (6.1)", ξ = m n(3n−2)/n⁴ − õ(1) → ξ = m n(3n−2)/n⁴ − (log n)^{−c₁} with c₁ chosen with C, D; reason: the õ(1) slack of (6.1) is the algorithm's choice
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: ℓ is the SoS level (§5.1 takes ℓ ≥ 4); at ℓ = 0 the degree bound would be 0
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m; reason: the polynomial bound is implied by m ≤ n²ℓ/(log n)^C ≤ n³
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 32 (PDF 34), Lemma 6.3

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 6.3 (premise of Lemma 5.3 for `k = 4`): for every `c > 0` there are `C, c₁, D > 0` and
`N₀` such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with `ℓ ≤ n/(log n)^C` and
`m ≤ n²ℓ/(log n)^C`, with probability at least `1 − (log n)^{−c}`, for
`ξ = m n(3n−2)/n⁴ − (log n)^{−c₁}` (6.1):
`𝒫_ξ ⊢_{Dℓ} ∑_i ⟨v_i,x⟩⁸ ≥ 1 − (log n)^{−c}` and `𝒫_ξ ⊢_{Dℓ} ∑_i ⟨v_i,x⟩⁶ ≤ 1 + (log n)^{−c}`. -/
theorem lemma_6_3 (c : ℝ) (hc : 0 < c) :
    ∃ C c₁ D : ℝ, 0 < C ∧ 0 < c₁ ∧ 0 < D ∧ ∃ N₀ : ℕ,
      ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
        (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
        (m : ℝ) ≤ (n : ℝ) ^ 2 * (ℓ : ℝ) / Real.log (n : ℝ) ^ C →
        1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
          SoSProves (D * (ℓ : ℝ)) (progP 4 v (xi4 n m (Real.log (n : ℝ) ^ (-c₁))))
            (R v 8 - MvPolynomial.C (1 - Real.log (n : ℝ) ^ (-c))) ∧
          SoSProves (D * (ℓ : ℝ)) (progP 4 v (xi4 n m (Real.log (n : ℝ) ^ (-c₁))))
            (MvPolynomial.C (1 + Real.log (n : ℝ) ^ (-c)) - R v 6)) := by sorry

end TensorBeyond.Main
