-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_epr_success_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.epr_success_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:16:48.129718+00:00
-- url     : https://prove2.me/theorems/34b464cc-886b-462c-b6de-97c3c3ba3c99
-- title:
--   Theorem 1.3: EPR probabilistic PBT asymptotics
-- statement:
--   Fix $d\ge1$. Let $p_d^{\mathrm{EPR}}(N)$ optimize exact heralded PBT success over measurements with resource exactly $N$ maximally entangled $d$-by-$d$ pairs. Let $G=X-\operatorname{tr}(X)I/d$, where $X$ is Hermitian with independent diagonal $N(0,1)$ coordinates and independent real and imaginary off-diagonal coordinates of variance $1/2$. Then
--   $$p_d^{\mathrm{EPR}}(N)=1-\sqrt{\frac d{N-1}}\,\mathbb E\lambda_{\max}(G)+o(N^{-1/2}).$$
--   Explicitly, for every $\eta>0$ the absolute remainder is at most $\eta/\sqrt N$ for all sufficiently large $N\ge2$. This describes the fixed-dimension EPR heralded error.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 6, Theorem 1.3: EPR probabilistic PBT asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Theorem 1.3, PDF p.6 (restated p.26): EPR resource, optimized heralded measurement.
N-1 lies inside the square root; the remainder is o(N^-1/2). -/
theorem epr_success_expansion (d : ℕ) (hd : 0 < d) :
    ∀ eta : ℝ, 0 < eta → ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0,
      |eprSuccess d N - 1 + Real.sqrt ((d : ℝ)/((N : ℝ)-1)) * expectedLargest d hd| ≤
        eta / Real.sqrt (N : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
