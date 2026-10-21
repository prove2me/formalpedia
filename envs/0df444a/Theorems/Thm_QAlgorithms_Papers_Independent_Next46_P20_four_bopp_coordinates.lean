-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_four_bopp_coordinates
-- name    : QAlgorithms.Papers.Independent.Next46.P20.four_bopp_coordinates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:26:52.212989+00:00
-- url     : https://prove2.me/theorems/1bb177dd-4a42-4b32-bc27-5c60edfe63f4
-- title:
--   Four Bopp conjugation identities and preserved commutators
-- statement:
--   Let $n\ge1$, let $U=U_D(-\log\sqrt2)U_R(-\pi/4)$, and let $X_j=x_j$, $P_j=p_j$, $\Xi_{x,j}=-i\partial_{x_j}$ and $\Xi_{p,j}=-i\partial_{p_j}$. Then
--   $$
--   UX_jU^{-1}=x_j+\tfrac i2\partial_{p_j},\quad
--   UP_jU^{-1}=p_j+\tfrac i2\partial_{x_j},
--   $$
--   $$
--   U\Xi_{x,j}U^{-1}=p_j-\tfrac i2\partial_{x_j},\quad
--   U\Xi_{p,j}U^{-1}=x_j-\tfrac i2\partial_{p_j}.
--   $$
--   The equalities identify the maximal weak $L^2$ graphs with the transported self-adjoint domains. On the common Schwartz core the transformed operators have $[\widetilde X_j,\widetilde\Xi_{x,k}]=i\delta_{jk}I$ and $[\widetilde P_j,\widetilde\Xi_{p,k}]=i\delta_{jk}I$; every other independent commutator is zero.
--
--   Thus all four fundamental operators, including the auxiliary pair, form the transported Heisenberg representation.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 22, Theorem 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF pp.22–23, Theorem 5.5: all four conjugation identities with maximal
transported domains, and every Heisenberg commutator on the Schwartz core. -/
theorem four_bopp_coordinates {n : ℕ} (hn : 0 < n) :
    (∀ (a : Fin 4) (j : Fin n),
      conjugatePhaseGraph moyalTransform (originalCoordinateGraph a j) = boppCoordinateGraph a j) ∧
    (∀ (a b : Fin 4) (j k : Fin n) (f : SchwartzMap (PhaseCoordinates n) ℂ) (z : PhaseCoordinates n),
      boppOnFunction a j (boppOnFunction b k (f : PhaseCoordinates n → ℂ)) z -
        boppOnFunction b k (boppOnFunction a j (f : PhaseCoordinates n → ℂ)) z =
      Complex.I * commutatorCoefficient a b j k * f z) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
