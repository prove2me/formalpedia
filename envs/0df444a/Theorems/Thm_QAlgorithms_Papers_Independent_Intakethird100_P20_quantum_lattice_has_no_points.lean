-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quantum_lattice_has_no_points
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.quantum_lattice_has_no_points
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:34:55.722212+00:00
-- url     : https://prove2.me/theorems/ac7dbd83-c02b-4faa-8f91-5ee1ebf35150
-- title:
--   Proposition 3.3
-- statement:
--   For a complex Hilbert space $H$ with $\dim H>1$, the complete lattice $L(H)$ of closed subspaces has no completely prime lattice points:
--
--   $$\nexists p\subseteq L(H)\quad p\text{ is a lattice point}.$$
--
--   The point condition preserves arbitrary joins. It is distinct from maximality of a proper filter base.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 38, Proposition 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.3; de Groote, Observables I, PDF p./pp. 38.
-/
theorem quantum_lattice_has_no_points {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hdim : 1 < Module.rank ℂ H) :
    ¬ ∃ p : Set (ClosedSubmodule ℂ H), IsLatticePoint p := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
