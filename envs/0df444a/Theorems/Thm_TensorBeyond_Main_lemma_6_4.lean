-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_6_4
-- name    : TensorBeyond.Main.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:23.191569+00:00
-- url     : https://prove2.me/theorems/fce3f23b-1753-48b9-9ba5-868826cbda50
-- title:
--   Lemma 6.4 — spider fight bound: $\{x_u^2=1\}\vdash_{O(\ell)}2s_4(x)-s_8(x)\le1+\tilde o(1)$
-- statement:
--   Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$ and $s_4,s_8$ the spider polynomials. For every $c>0$ there are $C,D>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le n^2\ell/(\log n)^C$, with probability at least $1-(\log n)^{-c}$,
--   $$\{x_u^2=1\ \forall u\in[n]\}\ \vdash_{D\ell}\ 2s_4(x)-s_8(x)\ \le\ 1+(\log n)^{-c}.$$
--   Combined with $s_4\ge1-\tilde o(1)$ under $\mathcal P_\xi$ it yields $s_8\ge 1-\tilde o(1)$, the core of the lower bound on the eighth moment in Lemma 6.3. It is proved by a sharp spectral bound on the level-$\ell$ Kikuchi matrix of $2s_4-s_8$.
--
--   Differences from the source:
--   - reading: 2s_4(x) − s_8(x) ≤ õ(1) → 2s_4(x) − s_8(x) ≤ 1 + (log n)^{−c}; reason: obvious typo, the printed form fails at the Boolean point x = v_1 (where 2s_4 − s_8 = 1 ± o(1)), and the proof of Lemma 6.3 uses s_8 ≥ 2s_4 − 1 − õ(1)
--   - reading: ℓ = õ(n), m = õ(n²ℓ), degree O(ℓ), "with high probability" → for every c there are C, D, N₀ with ℓ ≤ n/(log n)^C, m ≤ n²ℓ/(log n)^C, degree D·ℓ, probability ≥ 1 − (log n)^{−c}; reason: the paper's õ convention (p. 2) with "for every c", the stronger reading
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: ℓ is the SoS level (§5.1 takes ℓ ≥ 4); at ℓ = 0 the degree bound would be 0
--   - reading: standing assumption n ≤ m ≤ poly(n) of §4.1 → n ≤ m; reason: the polynomial bound is implied by m ≤ n²ℓ/(log n)^C ≤ n³
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 32 (PDF 34), Lemma 6.4

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 6.4 (spider fight bound), with the intended right-hand side `1 + õ(1)`: for every
`c > 0` there are `C, D > 0` and `N₀` such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with
`ℓ ≤ n/(log n)^C` and `m ≤ n²ℓ/(log n)^C`, with probability at least `1 − (log n)^{−c}`,
`{x_u² = 1} ⊢_{Dℓ} 2 s_4(x) − s_8(x) ≤ 1 + (log n)^{−c}`. -/
theorem lemma_6_4 (c : ℝ) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ (n : ℝ) ^ 2 * (ℓ : ℝ) / Real.log (n : ℝ) ^ C →
      1 - Real.log (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        SoSProves (D * (ℓ : ℝ)) []
          (MvPolynomial.C (1 + Real.log (n : ℝ) ^ (-c)) - (2 * spider v 4 - spider v 8))) := by sorry

end TensorBeyond.Main
