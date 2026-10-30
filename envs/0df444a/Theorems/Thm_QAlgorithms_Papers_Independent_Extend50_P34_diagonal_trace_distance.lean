-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_diagonal_trace_distance
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.diagonal_trace_distance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:44:18.550764+00:00
-- url     : https://prove2.me/theorems/dec1420b-3760-4aac-92ab-c590bf949feb
-- title:
--   Fact 2.1
-- statement:
--   Let $\eta,\lambda$ be probability vectors on $[d]$, $d\ge1$, and set $\rho=\operatorname{diag}(\eta)$ and $\sigma=\operatorname{diag}(\lambda)$. Then
--
--   $$d_{\rm tr}(\rho,\sigma)=d_{\rm TV}(\eta,\lambda).$$
--
--   Both distances include the factor $1/2$. This embeds classical statistical distance into quantum trace distance.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 10, Fact 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Fact 2.1, arXiv:1501.05028v1, PDF p.10.  -/
theorem diagonal_trace_distance
    (d : ℕ) (hd : 0 < d) (eta lambda : Fin d → ℝ)
    (heta : Learning.IsDistribution eta) (hlambda : Learning.IsDistribution lambda) :
    traceDistance (Matrix.diagonal fun i => (eta i : ℂ))
      (Matrix.diagonal fun i => (lambda i : ℂ)) = tv eta lambda := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
