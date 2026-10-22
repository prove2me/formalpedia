-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_smoothFixedReference_comparison
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.smoothFixedReference_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:27:19.904095+00:00
-- url     : https://prove2.me/theorems/a3f7614b-1dc1-4a14-8690-601b26e1b9dc
-- title:
--   Lemma A.3: smoothed version of fixed-reference comparison
-- statement:
--   Let $\rho_{XUQ}$ be a finite-dimensional density state classical on $X,U$, and let $\varepsilon\ge0$. Use the historical smoothing convention explicitly cited in [28], Definition 3.2.1: optimize fixed-reference min-entropy over positive operators $\tau$ with trace at most that of $\rho$ and full trace-norm distance at most $\varepsilon\operatorname{Tr}\rho$. Then
--   $$H_{\min}^\varepsilon(\rho_{XUQ}\mid\rho_U)\ge H_{\min}^\varepsilon(\rho_{XU}\mid\rho_U).$$
--   Both references are the original marginal $\rho_U$. This is neither purified-distance smoothing nor classical event deletion. The cited original pins the convention left implicit in the local paper; no change to the printed inequality is made.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 19, Lemma A.3: smoothed version of fixed-reference comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Lemma A.3, p.19: smoothed comparison with the ORIGINAL rho_U fixed on
both sides. The cited historical smoothing definition is verified in [28],
Definition 3.2.1; its reference operator is not replaced by the smoothed marginal.
The source proof's change to sigma_U is unnecessary for the stated inequality. -/
theorem smoothFixedReference_comparison {X U Q : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (blocks : (X × U) → Matrix Q Q ℂ) (hblocks : IsNormalizedCQBlocks blocks)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    smoothFixedMin (cqClassicalOperator blocks) (referenceMarginal blocks) epsilon ≤
      smoothFixedMin (reorderedCQ blocks) (referenceMarginal blocks) epsilon := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
