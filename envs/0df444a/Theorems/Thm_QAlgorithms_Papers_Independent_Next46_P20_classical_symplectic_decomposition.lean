-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_classical_symplectic_decomposition
-- name    : QAlgorithms.Papers.Independent.Next46.P20.classical_symplectic_decomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:15:01.144589+00:00
-- url     : https://prove2.me/theorems/b23a09f5-4180-4090-b9c5-086ba2dd367b
-- title:
--   Double-phase symplectic map and its Hamiltonian decomposition
-- statement:
--   Let $n\ge1$ and order double-phase coordinates as $Z=(x,p,\xi_x,\xi_p)\in\mathbb R^{4n}$. Equip this space with $\sigma_x\oplus\sigma_p$, where $\sigma((q,\xi),(q',\xi'))=\xi\cdot q'-q\cdot\xi'$. The map
--   $$
--   S(Z)=(x-\xi_p/2,p-\xi_x/2,p+\xi_x/2,x+\xi_p/2)
--   $$
--   is symplectic and satisfies $S=S_R(\pi/4)\circ S_D(\log\sqrt2)$. Here $S_D(s)$ multiplies $x,p$ by $e^s$ and $\xi_x,\xi_p$ by $e^{-s}$; $S_R(\theta)$ rotates both $(x,\xi_p)$ and $(p,\xi_x)$ by $(u,v)\mapsto(u\cos\theta-v\sin\theta,u\sin\theta+v\cos\theta)$. Both families are symplectic bijections and solve Hamilton's equations for
--   $$
--   H_D=x\cdot\xi_x+p\cdot\xi_p,\qquad H_R=-\xi_x\cdot\xi_p-x\cdot p,
--   $$
--   respectively.
--
--   This is the classical transformation used to relate the two quantum representations.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 5, §1.1: double-phase symplectic map and decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF pp.4–5, §1.1: S is symplectic, decomposes as R(pi/4)D(log sqrt(2)),
and D,R are symplectic Hamilton flows of the displayed Hamiltonians. -/
theorem classical_symplectic_decomposition {n : ℕ} (hn : 0 < n) :
    Function.Bijective (classicalS (n := n)) ∧
    (∀ z w : DoublePhase n, doubleSigma (classicalS z) (classicalS w) = doubleSigma z w) ∧
    (∀ z : DoublePhase n,
      classicalS z = classicalR (Real.pi / 4) (doublePhaseDilation (Real.log (Real.sqrt 2)) z)) ∧
    (∀ s : ℝ, Function.Bijective (doublePhaseDilation (n := n) s) ∧
      ∀ z w : DoublePhase n, doubleSigma (doublePhaseDilation s z) (doublePhaseDilation s w) = doubleSigma z w) ∧
    (∀ theta : ℝ, Function.Bijective (classicalR (n := n) theta) ∧
      ∀ z w : DoublePhase n, doubleSigma (classicalR theta z) (classicalR theta w) = doubleSigma z w) ∧
    (∀ (s : ℝ) (z : DoublePhase n), HasDerivAt (fun t => doublePhaseDilation t z)
      (hamiltonField dilationHamiltonian (doublePhaseDilation s z)) s) ∧
    (∀ (theta : ℝ) (z : DoublePhase n), HasDerivAt (fun t => classicalR t z)
      (hamiltonField rotationHamiltonian (classicalR theta z)) theta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
