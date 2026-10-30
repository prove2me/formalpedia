-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P24_symmetricQFT_precision
-- name    : QAlgorithms.Papers.Independent.Extend50.P24.symmetricQFT_precision
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:45:52.374761+00:00
-- url     : https://prove2.me/theorems/48b2e360-7ba2-4852-be84-a10ba28bbf41
-- title:
--   Precision-dependent uniform symmetric-group QFT
-- statement:
--   For every integer $n\geq1$, fix the Young orthonormal realizations of all irreducible representations of $S_n$, with their phases independent of the input and precision. Let $f_\lambda$ be the number of standard Young tableaux of shape $\lambda\vdash n$. In the convention where the first tableau coordinate carries the left regular action, define
--
--   $$
--   F_n|g\rangle=\sum_{\lambda\vdash n}\sqrt{\frac{f_\lambda}{n!}}
--   \sum_{T,U\in\operatorname{SYT}(\lambda)}\rho_\lambda(g)_{T,U}|\lambda,T,U\rangle.
--   $$
--
--   There is a choice of those realizations for all $n$, a single polynomial-time classical constructor, and a polynomial $p$, such that $F_n$ is unitary and every positive precision-bit request $t$ produces a finite universal-gate circuit $C_{n,t}$ with
--
--   $$
--   \operatorname{work}(C_{n,t})\leq p(1+n+t),\qquad
--   \|C_{n,t}E_{\mathrm{in}}v-E_{\mathrm{out}}F_nv\|_2\leq2^{-t}\|v\|_2
--   \quad\text{for every }v\in\mathbb C[S_n].
--   $$
--
--   The input is an encoded permutation, and both output indices are genuine standard tableaux. The encodings are injective at the chosen register width and include clean ancillary coordinates. The polynomial and constructor are independent of the input state. Taking $t=\lceil\log_2(1/\epsilon)\rceil$ gives the claimed polynomial dependence on $n$ and $\log(1/\epsilon)$ for $0<\epsilon<1$.
--
--   This records the precision analysis made explicit in §3.2; it does not assert an efficient Fourier transform for arbitrary finite groups.
-- source:
--   An efficient high dimensional quantum Schur transform, arXiv:1804.00055v2, PDF p. 10, §3.2 unnumbered result: precision-dependent symmetric-group QFT

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P24

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Extend50.P24

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 (boxContent)

/-- §3.2, PDF p.10: a uniform precision-dependent symmetric-group QFT.
One polynomial and one classical TM work for every n and precision request;
the Young phases are fixed before all precision requests. t bits give
operator-norm error at most 2^(-t), hence every 0<epsilon<1 by ceiling log2. -/
theorem symmetricQFT_precision :
    ∃ Y : (n : ℕ) → SymmetricModels n,
      (∀ n, 0 < n → IsUnitaryBetween (symmetricFourier (Y n))) ∧
      ∃ circuits : ℕ → ℕ → CompiledCircuit,
      ∃ p : Polynomial ℕ, ∃ generate : List Bool → List Bool,
        QAlgorithms.Complexity.PolyTimeComputable generate ∧
        ∀ n t, 0 < n → 0 < t →
          generate (requestCode n 1 t) = (circuits n t).code ∧
          (circuits n t).work ≤ p.eval (1 + n + t) ∧
          Approximates permutationCode symmetricCode (symmetricFourier (Y n))
            (circuits n t) ((2 : ℝ) ^ (-(t : ℤ))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P24

end
