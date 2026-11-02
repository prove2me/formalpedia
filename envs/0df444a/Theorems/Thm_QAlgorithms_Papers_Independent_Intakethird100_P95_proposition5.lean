-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_proposition5
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.proposition5
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:25:40.127832+00:00
-- url     : https://prove2.me/theorems/f896403e-adee-43a1-8052-caea73e9c311
-- title:
--   Proposition 5: exact PPT pure-state entanglement cost
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. The exact PPT formation cost $E_{xc}$ is the infimum of limiting normalized log input ranks for PPT protocols that prepare every block exactly, with positive block lengths tending to infinity. Then
--
--   $$E_{xc}^{\rm PPT}(\rho_\lambda)=S_{1/2}(\lambda).$$
--
--   The paper obtains this pure-state formula as an application of Audenaert–Plenio–Eisert [4].
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 4, Proposition 5: exact PPT pure-state entanglement cost

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF p.4, Proposition 5: EXACT formation cost, an application of Audenaert–Plenio–Eisert [4]. -/
theorem proposition5 {d : ℕ} (lam : Fin d → ℝ) (hprob : IsProbability lam) :
    pptEntanglementCost lam true = (schmidtRenyi (1 / 2) lam : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
