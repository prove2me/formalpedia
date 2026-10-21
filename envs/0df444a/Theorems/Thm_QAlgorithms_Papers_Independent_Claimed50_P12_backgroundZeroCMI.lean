-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_backgroundZeroCMI
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.backgroundZeroCMI
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T19:38:06.057565+00:00
-- url     : https://prove2.me/theorems/49b911aa-ea8e-437c-83bb-a01bf59fa384
-- title:
--   Zero conditional mutual information and exact recovery
-- statement:
--   For every density operator $\rho_{ABC}$ on nonzero finite-dimensional systems,
--
--   $$I(A:C|B)_\rho=0\quad\Longleftrightarrow\quad\exists T_{B\to BC}\ \mathrm{CPTP}:\ \rho_{ABC}=(\mathrm{id}_A\otimes T)(\rho_{AB}).$$
--
--   The input of the recovery map is the state's own $AB$ marginal, and the amplification retains entanglement with $A$. This characterizes the exact Markov property in the introduction.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 1, BackgroundZeroCMI

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Zero CMI characterizes exact recovery, Eq.1 and surrounding text (PDF pp.1–2).
The recovery acts on B with the identity on the entangled A register. -/
theorem backgroundZeroCMI {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Op (A × (B × C))) (hrho : IsDensityMatrix rho) : cmi rho = 0 ↔ Markov rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
