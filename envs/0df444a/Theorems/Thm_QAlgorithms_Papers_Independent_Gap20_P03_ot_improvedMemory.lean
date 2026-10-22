-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_ot_improvedMemory
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.ot_improvedMemory
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:23:26.335473+00:00
-- url     : https://prove2.me/theorems/23408f81-102d-4851-9dab-b77388d02077
-- title:
--   Unnumbered: improved sender-security memory tradeoff
-- statement:
--   Let $\ell(n),q(n)$ be nonnegative integer sequences. If there are $a>0$ and $N$ such that
--   $$an\le n/4-\ell(n)-q(n)\qquad(n\ge N),$$
--   then the Figure 1 protocol is sender-secure with a nonnegative negligible error function chosen uniformly before all receiver attacks. Each attack admits the classical binary extension required by Definition 4.4. The bound applies only to coherent memory immediately before step 3; classical information and the full final view are retained without a size bound.
--
--   This records the improved asymptotic tradeoff asserted on p.11 separately from Theorem 4.6. The cited proof technique is not an added hypothesis, and no finite-parameter formula is asserted.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 11, Unnumbered: improved sender-security memory tradeoff

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Section 4.3, p.11, asserted improved asymptotic tradeoff. The cited
technique is not a hypothesis, and no finite-parameter bound is invented for it. -/
theorem ot_improvedMemory (ell q : ℕ → ℕ) (hslack : OTLinearSlack 1 ell q) :
    ∃ epsilon : ℕ → ℝ, Negligible epsilon ∧
      ∀ n, OTSenderSecure n (ell n) (q n) (epsilon n) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
