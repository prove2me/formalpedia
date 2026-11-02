-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_proposition6
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.proposition6
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:26:27.376498+00:00
-- url     : https://prove2.me/theorems/17cfb158-78c4-400c-aa53-3436b73fcd67
-- title:
--   Proposition 6: three necessary PPT entropy inequalities
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. For a finite order $t$, $S_t$ is the Rényi entropy, with $S_0$ the log support size, $S_1=-\sum_i\lambda_i\log_2\lambda_i$ (using $0\log_2 0=0$), and $S_t=(1-t)^{-1}\log_2\sum_i\lambda_i^t$ otherwise. The separate infinity order is $S_\infty=-\log_2\max_i\lambda_i$. Let $\mu$ be another finite probability vector. If a deterministic exact PPT operation transforms $\rho_\mu$ to $\rho_\lambda$, then
--
--   $$S_{1/2}(\mu)\ge S_{1/2}(\lambda),\qquad S_1(\mu)\ge S_1(\lambda),\qquad S_\infty(\mu)\ge S_\infty(\lambda).$$
--
--   These are three necessary conditions for pure-state PPT conversion.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 4, Proposition 6: three necessary PPT entropy inequalities

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

/-- PDF p.4, Proposition 6, (11)–(13): all three necessary inequalities, from mu to lam. -/
theorem proposition6 {d e : ℕ} (mu : Fin d → ℝ) (lam : Fin e → ℝ)
    (hmu : IsProbability mu) (hlam : IsProbability lam) (hreach : Reach (schmidtDensity mu) (schmidtDensity lam)) :
    schmidtRenyi (1 / 2) lam ≤ schmidtRenyi (1 / 2) mu ∧ schmidtRenyi 1 lam ≤ schmidtRenyi 1 mu ∧
    renyiInfinity lam ≤ renyiInfinity mu := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
