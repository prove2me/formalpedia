-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_bb84_tightness
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.bb84_tightness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:16:56.367685+00:00
-- url     : https://prove2.me/theorems/3015effb-43e3-43bd-bf56-70f3d5b3fa21
-- title:
--   Unnumbered: asymptotic tightness of the BB84 relation
-- statement:
--   For each $n\ge0$, take the normalized density state $\rho=|0\rangle\langle0|^{\otimes n}$. Independently choose uniform BB84 bases $\Theta$ and let $X$ be its measurement outcome. Then
--   $$H(X\mid\Theta)=n/2.$$
--   Here $H$ is Shannon entropy in bits. This exact witness gives the upper benchmark for asymptotic tightness; it does not assert a nonsmooth min-entropy equality for arbitrary states.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 8, Unnumbered: asymptotic tightness of the BB84 relation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Section 3, p.8, tightness witness: |0><0| tensor n, and the exact n/2
conditional Shannon entropy. This is not a nonsmooth min-entropy equality. -/
theorem bb84_tightness (n : ℕ) :
    IsDensityMatrix (pureDensity (zeroKet n)) ∧
    conditionalShannon (measurementExperiment bb84Basis (pureDensity (zeroKet n))) =
      (n : ℝ)/2 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
