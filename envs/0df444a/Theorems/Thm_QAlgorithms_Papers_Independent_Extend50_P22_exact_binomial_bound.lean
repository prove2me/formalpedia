-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_exact_binomial_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.exact_binomial_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:24:29.905421+00:00
-- url     : https://prove2.me/theorems/743330b1-4e39-4590-872f-2c4d2a6c93cd
-- title:
--   Theorem 18: exact binomial approximate Eastin-Knill bound
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. Assume $d\ge2$ and covariance for the full defining logical $SU(d)$ action through a continuous transversal representation. Put $D=\max_i d_i$, $e_w=\epsilon_{\rm worst}$ and $e_a=\epsilon_e$. Both errors are strictly positive, and $$D\ge\binom{d-1+\lceil(2ne_w)^{-1}\rceil}{d-1},\qquad D\ge\binom{d-1+\lceil(nde_a)^{-1}\rceil}{d-1}.$$ The inverses are real reciprocals. These exact bounds precede the logarithmic approximate Eastin–Knill estimates.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 56, Theorem 18: exact binomial approximate Eastin-Knill bound

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.56–57, Theorem 18, (E.14),(E.15). Strict positivity precedes real reciprocals;
the ceiling is natural but the inverse is real. -/
theorem exact_binomial_bound {d n : ℕ} (c : CovariantErasureCodeData d n) (hd : 2 ≤ d)
    (hc : SUCovariant c) :
    0 < errorWorst c.uniformNoise ∧ 0 < errorE c.uniformNoise ∧
    Nat.choose (d - 1 + ⌈(2 * (n : ℝ) * errorWorst c.uniformNoise)⁻¹⌉₊) (d - 1) ≤ c.maxDim ∧
    Nat.choose (d - 1 + ⌈((n : ℝ) * d * errorE c.uniformNoise)⁻¹⌉₊) (d - 1) ≤ c.maxDim := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
