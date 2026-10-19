-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_stabilization_approximateOrbitViability
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.stabilization_approximateOrbitViability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:47:45.607975+00:00
-- url     : https://prove2.me/theorems/acb32abd-e49a-48e7-b7d2-147ec9f4e1b1
-- title:
--   Unnumbered full-system consequence of Theorem 3.8
-- statement:
--   If a GKSL reduced system on $\mathbb C^n$, $n\ge2$, is stabilizable, then every $SU(n)$ orbit of densities is approximately viable in the full system with fast full Hamiltonian controls. For every initial density $\rho_0$, horizon $T\ge0$, and $\varepsilon>0$, there is a full trajectory starting exactly at $\rho_0$ with
--
--   $$\forall t\in[0,T],\quad\exists U_t\in SU(n):\ \|\rho(t)-U_t\rho_0U_t^*\|\le\varepsilon.$$
--
--   The controls may depend on the initial state, horizon, and tolerance. No single constant Hamiltonian fixing every density is asserted.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 10, Unnumbered full-system consequence of Theorem 3.8

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

/-- arXiv:2308.00561v1, PDF p.10, Unnumbered full-system consequence of Theorem 3.8. Orbit distance uses a finite-dimensional matrix norm; arbitrary closeness is norm independent. The orbit witness may depend on time. -/
theorem stabilization_approximateOrbitViability {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (C : FullControls n) (h : stabilizableSystem D) : approximatelyViableOrbits D C := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
