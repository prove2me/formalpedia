-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_fixedReference_comparison
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.fixedReference_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:26:20.689703+00:00
-- url     : https://prove2.me/theorems/d99ea0df-94e1-42f6-b41b-25ade9071245
-- title:
--   Lemma A.2: fixed-reference unsmoothed quantum min-entropy
-- statement:
--   Let $\rho_{XUQ}$ be a finite-dimensional density state classical on $X,U$, with arbitrary conditional quantum states on $Q$. Let $\rho_{XU}$ and $\rho_U$ be its actual marginals. For a fixed positive reference $\sigma_B$, define $H_{\min}(\rho_{AB}\mid\sigma_B)$ as the extended supremum of real $r$ satisfying $2^{-r}I_A\otimes\sigma_B-\rho_{AB}\succeq0$. Then
--   $$H_{\min}(\rho_{XUQ}\mid\rho_U)\ge H_{\min}(\rho_{XU}\mid\rho_U).$$
--   The left unconditioned register is $XQ$ after permuting registers, and the same original reference $\rho_U$ is used on both sides. This is a fixed-reference comparison, without optimizing the reference.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 18, Lemma A.2: fixed-reference unsmoothed quantum min-entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Lemma A.2, pp.18-19. In the left entropy the unconditioned register is XQ,
not X; the conditioned reference remains the ORIGINAL rho_U on both sides. -/
theorem fixedReference_comparison {X U Q : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (blocks : (X × U) → Matrix Q Q ℂ) (hblocks : IsNormalizedCQBlocks blocks) :
    fixedMin (cqClassicalOperator blocks) (referenceMarginal blocks) ≤
      fixedMin (reorderedCQ blocks) (referenceMarginal blocks) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
