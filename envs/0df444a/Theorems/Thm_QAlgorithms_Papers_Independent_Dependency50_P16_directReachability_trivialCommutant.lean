-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_directReachability_trivialCommutant
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.directReachability_trivialCommutant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:26:55.915865+00:00
-- url     : https://prove2.me/theorems/035f683e-92dd-47e5-a757-773484626967
-- title:
--   Corollary 4.15: A partial converse under trivial commutant
-- statement:
--   Let $F$ be a proper nonempty face of $\Delta^{n-1}$ with $d$ supported coordinates. If the commutant of $\{H_0,V_1,\ldots,V_r\}$ consists only of scalar matrices and $F$ is directly reachable, then
--
--   $$\exists S\subseteq\mathbb C^n:\quad\dim S=d,\quad S\text{ lazy},\quad S\text{ not an enclosure}.$$
--
--   This is a necessary condition under the extra commutant hypothesis; no converse is asserted.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 19, Corollary 4.15: A partial converse under trivial commutant

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

/-- arXiv:2308.00561v1, PDF p.19, Corollary 4.15: A partial converse under trivial commutant.  -/
theorem directReachability_trivialCommutant {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (F : Face n) (hproper : F.support.card < n) (hc : trivialCommutant D)
    (hF : directlyReachable D F) :
    ∃ S : Submodule ℂ (Hilbert n), lazy D.jump S ∧ Module.finrank ℂ S = F.support.card ∧
      ¬enclosure D S := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
