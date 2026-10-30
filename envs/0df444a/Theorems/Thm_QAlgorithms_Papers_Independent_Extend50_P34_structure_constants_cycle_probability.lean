-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_structure_constants_cycle_probability
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.structure_constants_cycle_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:53:26.728563+00:00
-- url     : https://prove2.me/theorems/6b1c60d5-3cf9-4ba4-b10c-88cd6e3a52a1
-- title:
--   Corollary 2.37
-- statement:
--   For partitions $\mu\vdash r_1$, $\nu\vdash r_2$, $\tau\vdash t$ of positive sizes, put $C^t_{r_1r_2}=r_1!r_2!/[(t-r_1)!(t-r_2)!(r_1+r_2-t)!]$ when $r_1,r_2\le t\le r_1+r_2$, and zero otherwise. In the valid range,
--
--   $$f_{\mu\nu}^{\tau}=C^t_{r_1r_2}\Pr[w_1w_2\text{ has cycle type }\tau].$$
--
--   Here $w_1,w_2$ are independent uniform permutations of cycle types $\mu,\nu$ on the first $r_1$ and last $r_2$ positions of $[t]$, extended by fixed points. Outside the valid range the structure constant is zero. This expresses multiplication of central-character observables as a genuine cycle-class probability. The constants are defined by $p_\mu^\sharp p_\nu^\sharp=\sum_\tau f_{\mu\nu}^{\tau}p_\tau^\sharp$, equivalently by the partial-permutation factorization counts of Proposition 2.36.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 28, Corollary 2.37

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Corollary 2.37, arXiv:1501.05028v1, PDF p.28. Use Proposition 2.36 factorization counts to define f independently. Probability is used only in the valid range, and fixed points count as cycles. -/
theorem structure_constants_cycle_probability
    (mu nu tau : YoungDiagram) (hmu : 0 < mu.card)
    (hnu : 0 < nu.card) (htau : 0 < tau.card) :
    (∀ h : OverlapRange mu.card nu.card tau.card,
      structureConstant mu nu tau = overlapCoefficient mu.card nu.card tau.card *
        classProductProbability mu nu tau h) ∧
    (¬ OverlapRange mu.card nu.card tau.card → structureConstant mu nu tau = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
