-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_eq_45
-- name    : TDHamSim.QueryOptimal.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:22:56.000198+00:00
-- url     : https://prove2.me/theorems/9e9ff10a-30dd-42df-87ab-597cf85e6c63
-- title:
--   §5.2, eq. (45) — combination identity
-- statement:
--   Under the standing Hamiltonian assumptions, fix a $b$-qubit reuse register and finitely many real coefficients $\lambda_1,\ldots,\lambda_L$ with $L<2^b$ and sum one. Put $\widetilde U=\sum_N\lambda_NP_N$ and $E(A)=\sum_N\lambda_NG_N(A)$. Then
--
--   $$U_C-\widetilde U=CE(A)\Gamma,$$
--   $$\|U_C-\widetilde U\|\le\|C\|\,\|E(A)\|\,\|\Gamma\|\le\sqrt{\alpha T}\,\|E(A)\|.$$
--
--   The identity and both successive norm estimates are included, with signed coefficients permitted.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: an unspecified unitary completion of a uniform state preparation F_N → the explicit real Householder completion of that uniform column; reason: P_N depends only on the uniform column; this fixes a source choice without changing the encoded operator
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), §5.2, eq. (45) — combination identity, p.20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- §5.2, eq. (45), p.20: the identity and both norm inequalities. -/
theorem eq_45 {n a L : ℕ} (m b : ℕ) (H : ℝ → Mat (Bits n))
    (O : Fin (2^m) → Mat (Bits a × Bits n)) (α β T : ℝ) (coeff : Fin L → ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hw : stepWeight α T (2^m) ≤ 1)
    (hH : IsHamiltonian H α β T) (hO : IsHAMT H α T O)
    (hL : L < 2^b) (hcoeff : ∑ r, coeff r = 1) :
    let w := stepWeight α T (2^m)
    let E := combinedG coeff (privateBlock w O)
    cayleyProduct H α T (2^m) - combine b w O coeff = crossBlock w O * E * gamma H α T O ∧
      opNorm (cayleyProduct H α T (2^m) - combine b w O coeff) ≤
        opNorm (crossBlock w O) * opNorm E * opNorm (gamma H α T O) ∧
      opNorm (crossBlock w O) * opNorm E * opNorm (gamma H α T O) ≤ Real.sqrt (α*T)*opNorm E := by sorry

end TDHamSim.QueryOptimal
