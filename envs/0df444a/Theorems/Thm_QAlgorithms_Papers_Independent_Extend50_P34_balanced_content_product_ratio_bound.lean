-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_balanced_content_product_ratio_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.balanced_content_product_ratio_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:07:11.593504+00:00
-- url     : https://prove2.me/theorems/6aee658b-e23c-4212-a1a6-a05188bf30ca
-- title:
--   Proposition 4.20
-- statement:
--   Let $d\ge1$ and let $\mu\vdash k$ be balanced with $0<\ell(\mu)\le d$. Then
--
--   $$\frac{d^{\uparrow[\mu]_{\rm even}}}{d^{\uparrow[\mu]_{\rm odd}}}\le2^{k/2}.$$
--
--   The height condition makes every factor positive, and balancedness makes $k$ even. This controls the content-product ratio in the exact chi-squared expansion.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 43, Proposition 4.20

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 4.20, arXiv:1501.05028v1, PDF p.43. Each removed domino has neighboring signed contents and a positive-factor ratio at most 2. -/
theorem balanced_content_product_ratio_bound
    (d : ℕ) (hd : 0 < d) (mu : YoungDiagram) (hbalanced : DominoBalanced mu)
    (hheight0 : 0 < mu.colLen 0) (hheight : mu.colLen 0 ≤ d) :
    parityProduct d mu true / parityProduct d mu false ≤ (2 : ℝ)^(mu.card/2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
