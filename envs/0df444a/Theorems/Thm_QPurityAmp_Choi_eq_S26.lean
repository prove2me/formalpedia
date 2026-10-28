-- Prove2me | Theorems.Thm_QPurityAmp_Choi_eq_S26
-- name    : QPurityAmp.Choi.eq_S26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:24.937109+00:00
-- url     : https://prove2.me/theorems/ff96137a-b75f-4edb-983d-662812bd3246
-- title:
--   Eq. (S26), p. 20 — on the block [µ_i], C′ acts as c′_i = −S^[µ_i](a,…,a,b), a = λ/d, b = 1 − (d−1)λ/d
-- statement:
--   Let $d\ge 1$, $0<\lambda<1$, let $\varsigma$ be a Young diagram with $n$ boxes and at most $d$ rows, and let $i$ be a feasible row of $\varsigma$. Write
--   $$a=\frac{\lambda}{d},\qquad b=1-\frac{d-1}{d}\lambda$$
--   for the two eigenvalues of the depolarized state, and $Q_{\varsigma,i}=P_{\mu_i}(\mathbb I_{\mathrm{out}}\otimes\Pi_\varsigma)$ for the block $[\mu_i]$ of the $\varsigma$-sector. Then the modified cost matrix $C'$ acts on this block as the scalar $c_i'$:
--   $$Q_{\varsigma,i}\,C'\,Q_{\varsigma,i}=c'_i\,Q_{\varsigma,i},\qquad c'_i=-\frac{s^{[\nu_i]}(a,\dots,a,b)}{a^{d-1}b\;d^{[\nu_i]}}=-S^{[\mu_i]}(a,\dots,a,b),$$
--   where $s^{[\nu]}$ is the Schur polynomial in $d$ variables, $d^{[\nu]}$ the dimension of the irrep, and $\nu_i=\mu_i+(1^d)$.
--
--   Together with Eq. (S28) this identifies which coefficient of the linear program is largest, and hence the optimal block.
--
--   **Formalization Note** The irreps $\rho^{[\mu_i]}$ of the paper are rational: $\mu_i$ may have last row $-1$. They are encoded by the determinant shift: $s^{[\mu_i]}(x)=s^{[\nu_i]}(x)/\det(x)$ with $\det(x)=a^{d-1}b$, and $d^{[\mu_i]}=d^{[\nu_i]}$. For rows with $\mu_i$ a genuine Young diagram this is exactly the printed $-S^{[\mu_i]}(a,\dots,a,b)$. The block-scalar form $QC'Q=c'_iQ$ is the meaning of the coefficient $c'_i$ in the decomposition of Proposition S2.1.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 20, Eq. (S26) and the paragraph above it

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix Kronecker

open QAlgorithms.Schur

/-- Eq. (S26), p. 20: on the block [µ_i] of the ς-sector, the modified cost matrix C′ acts as
the scalar c′_i = −S^[µ_i](a, …, a, b), a = λ/d, b = 1 − (d−1)λ/d. With the determinant shift
ν_i = µ_i + (1^d): S^[µ_i](x) = s^[ν_i](x) / (det(x) · d^[ν_i]), det(x) = a^{d−1} b. -/
theorem eq_S26 {d n : ℕ} [NeZero d] (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1)
    (vs : Partition d n) (i : {i : Fin d // IsFeasibleRow vs i}) :
    blockProj vs i * costPrime d n lam * blockProj vs i =
      ((-(MvPolynomial.eval
              (fun j : Fin d => if j.val + 1 = d then 1 - (d - 1) * lam / d else lam / d)
              (schurPolynomial (shifted vs i)) /
            ((lam / d) ^ (d - 1) * (1 - (d - 1) * lam / d) *
              schurDimension (shifted vs i))) : ℝ) : ℂ) •
        blockProj vs i := by sorry

end QPurityAmp.Choi
