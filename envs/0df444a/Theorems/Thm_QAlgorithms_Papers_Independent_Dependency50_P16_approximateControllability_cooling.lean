-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_approximateControllability_cooling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.approximateControllability_cooling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:29:23.83685+00:00
-- url     : https://prove2.me/theorems/52dd2eea-8d7c-47bb-a49d-d5614525c118
-- title:
--   Proposition 4.20: Approximate controllability and forward/reverse cooling
-- statement:
--   For a GKSL generator with fast full Hamiltonian controls on $\mathbb C^n$, $n\ge2$, the following are equivalent:
--
--   $$\text{(R) approximately controllable}\quad\Longleftrightarrow\quad\text{(R) asymptotically coolable and reverse coolable}\quad\Longleftrightarrow\quad\text{(B) approximately controllable}.$$
--
--   Reverse coolability means that the closure of the forward reachable set from $e_1$ contains the ordered Weyl chamber. It does not mean evolving with negative dissipation.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 21, Proposition 4.20: Approximate controllability and forward/reverse cooling

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.21, Proposition 4.20: Approximate controllability and forward/reverse cooling.  -/
theorem approximateControllability_cooling {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (C : FullControls n) (i0 : Fin n) (hi0 : i0.val = 0) :
    List.TFAE [controllableR D, coolable D i0 ∧ reverseCoolable D i0, controllableB D C] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
