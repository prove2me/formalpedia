-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_unital_closedReachabilityLift
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.unital_closedReachabilityLift
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:48:51.416413+00:00
-- url     : https://prove2.me/theorems/6b9b9434-c009-40a6-aa4b-7f7942d8b9ec
-- title:
--   Unnumbered lift of the unital reachability trichotomy
-- statement:
--   For a unital GKSL generator on $\mathbb C^n$, $n\ge2$, with fast full Hamiltonian controls, and any normalized initial density $\rho_0$,
--
--   $$\overline{\operatorname{reach}_B(\rho_0)}=\{U\operatorname{diag}(\lambda)U^*:U\in SU(n),\ \lambda\in\overline{\operatorname{reach}_C(\operatorname{spec}^{\downarrow}\rho_0)}\}.$$
--
--   Thus the unital spectral reachability trichotomy lifts to full density matrices with entire unitary orbits included. The equality is for all-time closed reachable sets.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 26, Unnumbered lift of the unital reachability trichotomy

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

/-- arXiv:2308.00561v1, PDF p.26, Unnumbered lift of the unital reachability trichotomy. There is no Weyl ordering imposed on density matrices themselves. All-time closures permit arbitrarily fast initial and final unitary motion. -/
theorem unital_closedReachabilityLift {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (C : FullControls n) (hu : unital D) (rho : Mat n) (hrho : QAlgorithms.IsDensityMatrix rho) :
    closure (reachB D C rho) = orbitSaturation (closure (reachC D (densitySpectrum rho))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
