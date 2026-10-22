-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P03_logarithmic_inversion
-- name    : QAlgorithms.Papers.Independent.Gap20.P03.logarithmic_inversion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:25:47.240837+00:00
-- url     : https://prove2.me/theorems/769459fd-7662-47a5-82be-fb26f8cc3151
-- title:
--   Lemma A.1: logarithmic inversion estimate
-- statement:
--   Let $x$ be real with $0<x<1/e$, and define $y=x\log_2(1/x)$. If $y<1/4$, then
--   $$x>\frac{y}{4\log_2(1/y)}.$$
--   Here $e=\exp(1)$ and $y$ is constructed from $x$. These assumptions imply $y>0$ and a positive denominator. This elementary inversion estimate fixes the truncation constant in entropy accumulation.
-- source:
--   A Tight High-Order Entropic Quantum Uncertainty Relation With Applications, arXiv:quant-ph/0612014v2, PDF p. 17, Lemma A.1: logarithmic inversion estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

/-- Lemma A.1, pp.17-18: y is constructed from x, not an independent parameter. -/
theorem logarithmic_inversion (x : ℝ) (hx : 0 < x) (hxUpper : x < 1/Real.exp 1)
    (hy : x * Real.logb 2 (1/x) < 1/4) :
    let y := x * Real.logb 2 (1/x)
    y / (4 * Real.logb 2 (1/y)) < x := by sorry

end QAlgorithms.Papers.Independent.Gap20.P03

end
