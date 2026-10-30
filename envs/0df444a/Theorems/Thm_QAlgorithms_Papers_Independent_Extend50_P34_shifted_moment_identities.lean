-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_shifted_moment_identities
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.shifted_moment_identities
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:57:11.583977+00:00
-- url     : https://prove2.me/theorems/8f422a75-0751-44ed-be17-eb07c7d53d66
-- title:
--   Fact 3.7
-- statement:
--   For every real shift $c$ and partition $\lambda$, define $p^*_{k,c}(\lambda)=\sum_{i\ge1}[(\lambda_i-i-c)^k-(-i-c)^k]$. Then
--
--   $$p^*_{2,c}=(-2c-1)p_1^\sharp+p_2^\sharp,$$
--   $$p^*_{4,c}=(-4c^3-6c^2-4c-1)p_1^\sharp+(6c^2+6c+4)p_2^\sharp+(-6c-3)p_{(1,1)}^\sharp+(-4c-2)p_3^\sharp+4p_{(2,1)}^\sharp+p_4^\sharp.$$
--
--   These are identities of observables on all Young diagrams. They permit exact low-moment calculations under Schur sampling.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 31, Fact 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Fact 3.7, arXiv:1501.05028v1, PDF p.31. At c=-1/2 the quartic becomes pStar4=pSharp4+4pSharp(2,1)+(5/2)pSharp2, matching equation (14). -/
theorem shifted_moment_identities
    (c : ℝ) (lambda : YoungDiagram) :
    starShift 2 c lambda = (-2*c-1)*sharpParts {1} lambda + sharpParts {2} lambda ∧
    starShift 4 c lambda =
      (-4*c^3-6*c^2-4*c-1)*sharpParts {1} lambda +
      (6*c^2+6*c+4)*sharpParts {2} lambda +
      (-6*c-3)*sharpParts {1,1} lambda + (-4*c-2)*sharpParts {3} lambda +
      4*sharpParts {2,1} lambda + sharpParts {4} lambda := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
