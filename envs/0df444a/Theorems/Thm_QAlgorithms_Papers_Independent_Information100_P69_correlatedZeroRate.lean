-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_correlatedZeroRate
-- name    : QAlgorithms.Papers.Independent.Information100.P69.correlatedZeroRate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:07:23.726777+00:00
-- url     : https://prove2.me/theorems/b4b945cf-c90b-4400-b9cb-653b6ccb4dd8
-- title:
--   Correlated alternatives with zero Stein rate
-- statement:
--   Take one-dimensional input, a faithful output state $\omega$, a normalized vector $\phi$ with $\rho=|\phi\rangle\langle\phi|\ne\omega$, and $0<c<1$. Set $\zeta_k=c\rho^{\otimes k}+(1-c)\omega^{\otimes k}$. Define $\mathcal F_n$ as the convex hull over all partitions of the labeled sites, independently assigning either $\zeta_k$ or $\omega^{\otimes k}$ to each size-$k$ block. This specified family satisfies F1–F5,
--   $$\mathcal F_1=\operatorname{conv}\{\omega,c\rho+(1-c)\omega\},\quad\rho\notin\mathcal F_1,$$
--   and for all positive $n$ and $0<\varepsilon<1$,
--   $$\zeta_n\in\mathcal F_n,\quad\zeta_n\ge c\rho^{\otimes n},\quad0\le E_n\le\log_2(1/c),\quad\beta_{\varepsilon,n}\ge c(1-\varepsilon),\quad R_{\mathcal F}(\rho)=0.$$
--   This constructs a target outside the one-use free set with vanishing rate caused by correlations.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 24, Example 24

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Example 24, the specified correlated alternative family, PDF p.24.
All five axioms, the one-use convex hull, exclusion of rho, the uniform finite-block
bounds, and zero rate are asserted for the constructed family. -/
theorem correlatedZeroRate [Nonempty B] (omega : Matrix B B ℂ) (homega : Faithful omega)
    (phi : EuclideanSpace ℂ B) (hphi : ‖phi‖ = 1) (hne : pureDensity phi ≠ omega)
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    let rho := pureDensity phi
    let F := correlatedFamily rho omega c
    let N : Superop (Fin 1) B := replacer rho
    Admissible F omega ∧ Additional F (1 : Matrix (Fin 1) (Fin 1) ℂ) ∧
    F 1 = convexHull ℝ ({replacer (matrixPower omega 1), replacer (zeta rho omega c 1)} :
      Set (Superop (Sites (Fin 1) 1) (Sites B 1))) ∧
    power N 1 ∉ F 1 ∧
    (∀ n, 1 ≤ n → replacer (zeta rho omega c n) ∈ F n ∧
      (zeta rho omega c n-(c:ℂ) • matrixPower rho n).PosSemidef ∧
      0 ≤ resourceEntropy (power N n) (F n) ∧
      resourceEntropy (power N n) (F n) ≤ ENNReal.ofReal (Real.logb 2 (1/c)) ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 → c*(1-eps) ≤ beta (power N n) (F n) eps) ∧
    rate N F = 0 := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
