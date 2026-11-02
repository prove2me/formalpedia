-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_proposition3
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.proposition3
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:23:48.158198+00:00
-- url     : https://prove2.me/theorems/ec332f76-c417-4327-a0c6-94f9e5feff84
-- title:
--   Proposition 3: PPT asymptotic pure-state cost and distillation
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. Define PPT formation cost $E_c$ as the infimum, and PPT distillation $E_d$ as the supremum, of limiting rates $\lim_j(\log_2 K_j)/n_j$ along PPT protocols with positive block lengths $n_j\to\infty$, positive integer resource ranks $K_j$, and trace norm error tending to zero. Rank-one resources are permitted for zero entanglement. Then
--
--   $$E_c^{\rm PPT}(\rho_\lambda)=E_d^{\rm PPT}(\rho_\lambda)=S_1(\lambda).$$
--
--   This identifies the reversible asymptotic pure-state entanglement rate under PPT operations.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 3, Proposition 3: PPT asymptotic pure-state cost and distillation

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

/-- PDF p.3, Proposition 3: vanishing-error PPT cost and distillation both equal Shannon entropy. -/
theorem proposition3 {d : ℕ} (lam : Fin d → ℝ) (hprob : IsProbability lam) :
    pptEntanglementCost lam false = (schmidtRenyi 1 lam : EReal) ∧
    pptDistillableEntanglement lam false = (schmidtRenyi 1 lam : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
