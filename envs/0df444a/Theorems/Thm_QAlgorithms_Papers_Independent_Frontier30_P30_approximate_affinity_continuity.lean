-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_approximate_affinity_continuity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.approximate_affinity_continuity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:33:00.102643+00:00
-- url     : https://prove2.me/theorems/6a8b423b-2d87-49e0-9bd6-06e528c63d18
-- title:
--   Approximate affinity and subextensivity imply the finite continuity estimate
-- statement:
--   Let $f_d$ be a real functional on the normalized density matrices of every positive finite dimension $d$. Fix constants $c,M\ge0$, independent of dimensions, states and mixing weights. Suppose that for every such system, every two densities $\rho,\sigma$, and every $p\in[0,1]$, the absolute binary mixing defect is at most $c$ and $|f_d(\rho)|\le M\log_2 d$. Then every pair of densities on the same system satisfies
--
--   $$|f_d(\rho_1)-f_d(\rho_2)|\le M\|\rho_1-\rho_2\|_1\log_2 d+4c.$$
--
--   Here $\|\cdot\|_1$ is the full trace norm. This is the source's estimate for its growing-dimension asymptotic regime; positive fixed $c$ does not give a vanishing fixed-dimensional continuity modulus.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 3, Proposition 2, Eq. (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF p.3, Proposition 2, (13).
Retain 4c; this is not a fixed-dimensional vanishing continuity modulus. -/
theorem approximate_affinity_continuity (f : Functional) (c M : ℝ)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (haff : ApproximateAffinity f c) (hsub : Subextensive f M) :
    ∀ d : ℕ, 0 < d → ∀ rho sigma : Op (Fin d),
      IsDensityMatrix rho → IsDensityMatrix sigma →
      |f d rho-f d sigma| ≤ M * traceNorm (rho-sigma) * log2 d + 4*c := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
