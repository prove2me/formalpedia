-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_dilation_evolution_group
-- name    : QAlgorithms.Papers.Independent.Next46.P20.dilation_evolution_group
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:24:26.377653+00:00
-- url     : https://prove2.me/theorems/d12b3bb3-83aa-463c-8521-30cd2a8ceea1
-- title:
--   Dilation unitary group and its maximal differential generator
-- statement:
--   Let $n\ge1$ and let $H_D=-i(x\cdot\partial_x+p\cdot\partial_p+n)$ have its maximal distributional $L^2(\mathbb R^{2n})$ domain. The formula
--   $$
--   (U_D(s)\Psi)(x,p)=e^{-ns}\Psi(e^{-s}x,e^{-s}p),\qquad s\in\mathbb R,
--   $$
--   defines a strongly continuous one-parameter unitary group with generator $H_D$. More precisely, $\Psi\in D(H_D)$ and $H_D\Psi=\Phi$ if and only if the Hilbert-norm derivative of $s\mapsto U_D(s)\Psi$ at zero exists and equals $-i\Phi$.
--
--   The formula is an almost-everywhere identity of $L^2$ representatives; its amplitude compensates the change of volume in $2n$ variables.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 19, Theorem 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.19, Theorem 5.2: the explicit dilation formula gives the strongly
continuous unitary group with the full maximal L2 differential generator. -/
theorem dilation_evolution_group {n : ℕ} (hn : 0 < n) :
    (∀ s : ℝ, RealizesL2Formula (dilationFormula (n := n) s) (dilationEvolution s)) ∧
    strongUnitaryGroup (dilationEvolution (n := n)) ∧
    generatesGraph (dilationEvolution (n := n)) (weakPhaseGraph dilationTestAction) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
