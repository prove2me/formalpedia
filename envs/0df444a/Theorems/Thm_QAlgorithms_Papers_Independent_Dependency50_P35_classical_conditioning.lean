-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_classical_conditioning
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.classical_conditioning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:04:43.69795+00:00
-- url     : https://prove2.me/theorems/567b8734-fec4-4f85-b2fc-79a5bc386a7b
-- title:
--   Proposition 9: entropy conditioned on a classical register
-- statement:
--   Let $\alpha\in[1/2,1)\cup(1,\infty)$, let $p$ be a probability distribution on a finite classical register $Y$, and let every $\rho_{AB}^y$ be a normalized PSD state. For $\rho_{ABY}=\bigoplus_y p_y\rho_{AB}^y$,
--
--   $$
--   \widetilde H_\alpha(A|BY)_\rho=\frac{\alpha}{1-\alpha}\log_2\sum_y p_y\,2^{\frac{1-\alpha}{\alpha}\widetilde H_\alpha(A|B)_{\rho^y}}.
--   $$
--
--   Every block conditional entropy is finite, and zero-probability blocks contribute zero. The printed proposition leaves the order unbound; this range is selected from the measurement data-processing step in its proof on PDF p.24.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 12, Proposition 9

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF pp.12,24, Proposition 9: the unbound printed order is interpreted using
the proof's measurement-DPI step. All block conditional entropies are finite,
so their toReal conversions retain their complete values. -/
theorem classical_conditioning {A B Y : Type} [Fintype A] [Fintype B] [Fintype Y]
    [DecidableEq A] [DecidableEq B] [DecidableEq Y]
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a ∧ a ≠ 1)
    (p : Distribution Y) (rho : Y → Mat (A × B)) (hr : ∀ y, Density (rho y)) :
    conditionalRenyi a (cqConditional p.val rho) =
      (a / (1-a) * Real.logb 2 (∑ y, p.val y * (2 : ℝ) ^
        (((1-a)/a) * (conditionalRenyi a (rho y)).toReal)) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
