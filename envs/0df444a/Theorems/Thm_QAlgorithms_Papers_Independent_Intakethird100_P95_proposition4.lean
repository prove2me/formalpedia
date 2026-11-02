-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_proposition4
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.proposition4
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:24:47.086348+00:00
-- url     : https://prove2.me/theorems/e42fb569-d3ec-416e-8d17-9fbe1ad4a0ef
-- title:
--   Proposition 4: exact PPT distillable entanglement
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. The exact PPT distillable entanglement $E_{xd}$ is the supremum of limiting normalized log output ranks of PPT distillation protocols with positive block lengths tending to infinity and zero error at every block. Rank-one output represents rate zero. Then
--
--   $$E_{xd}^{\rm PPT}(\rho_\lambda)=S_\infty(\lambda).$$
--
--   This distinguishes exact asymptotic concentration from concentration with vanishing error.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 3, Proposition 4: exact PPT distillable entanglement

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

/-- PDF pp.3–4, Proposition 4: exact distillation, not vanishing-error distillation. -/
theorem proposition4 {d : ℕ} (lam : Fin d → ℝ) (hprob : IsProbability lam) :
    pptDistillableEntanglement lam true = (renyiInfinity lam : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
