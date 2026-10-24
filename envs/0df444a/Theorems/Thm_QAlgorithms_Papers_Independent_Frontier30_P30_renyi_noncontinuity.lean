-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_renyi_noncontinuity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.renyi_noncontinuity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:35:29.724171+00:00
-- url     : https://prove2.me/theorems/2810e6e8-45ac-4af5-8faa-af8b7b195a53
-- title:
--   Explicit typical-spectrum witness to Renyi noncontinuity for orders below one
-- statement:
--   Fix $0\le\alpha<1$ and the qubit density $\rho=\operatorname{diag}(1/4,3/4)$. Let $S$ be von Neumann entropy in bits and $S_\alpha$ Renyi entropy, with $S_0=\log_2\operatorname{rank}$. In the original $2^n$-dimensional space, retain the eigenvalues $w$ of $\rho^{\otimes n}$ for which $|-(\log_2 w)/n-S(\rho)|\le n^{-1/4}$, and normalize them, obtaining $\rho_{\mathrm{typ},n}$. Use the original density if no eigenvalue is retained; at $n=0$ retain the scalar state. Both sequences consist of density matrices, and
--
--   $$\|\rho_{\mathrm{typ},n}-\rho^{\otimes n}\|_1\longrightarrow0,\quad \frac{S_\alpha(\rho_{\mathrm{typ},n})}{n}\longrightarrow S(\rho),\quad \frac{S_\alpha(\rho^{\otimes n})}{n}\longrightarrow S_\alpha(\rho).$$
--
--   Moreover their absolute entropy difference divided by $n=\log_2(2^n)$ converges to $S_\alpha(\rho)-S(\rho)>0$. This explicitly witnesses failure of asymptotic continuity, including the support-rank endpoint.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 4, Examples, typical-eigenvalue construction

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF p.4, Examples. Entropy tending to n S(rho)
is read as convergence of the entropy rate. Spectrum (1/4,3/4) and window
n^(-1/4) make the source's typical-eigenvalue construction explicit. -/
theorem renyi_noncontinuity (alpha : ℝ) (ha : 0 ≤ alpha) (hb : alpha < 1) :
    (∀ n, IsDensityMatrix (qubitCopies n) ∧ IsDensityMatrix (typicalCopies n)) ∧
    Tendsto (fun n => traceNorm (typicalCopies n-qubitCopies n)) atTop (nhds 0) ∧
    Tendsto (fun n => Dependency50.P05.renyiEntropy alpha (typicalCopies n)/(n : ℝ))
      atTop (nhds witnessEntropy) ∧
    Tendsto (fun n => Dependency50.P05.renyiEntropy alpha (qubitCopies n)/(n : ℝ))
      atTop (nhds (Dependency50.P05.renyiEntropy alpha (qubitCopies 1))) ∧
    0 < Dependency50.P05.renyiEntropy alpha (qubitCopies 1)-witnessEntropy ∧
    Tendsto (fun n => |Dependency50.P05.renyiEntropy alpha (qubitCopies n)-
      Dependency50.P05.renyiEntropy alpha (typicalCopies n)|/(n : ℝ)) atTop
      (nhds (Dependency50.P05.renyiEntropy alpha (qubitCopies 1)-witnessEntropy)) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
