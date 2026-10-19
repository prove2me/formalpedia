-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_wellSpreadDepth
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.wellSpreadDepth
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:36:45.118989+00:00
-- url     : https://prove2.me/theorems/d7d2883a-985c-4c76-b75c-858164701afe
-- title:
--   Fact 4: depth lower bound for well-spread distributions
-- statement:
--   Let $P$ be a circuit of depth $t$ consisting of layers of disjoint one- and two-qubit unitaries, starting in the all-zero product state. Allow any number of clean ancillas and measure only its $n>0$ output qubits in the standard basis, giving distribution $D$. Let $0<\mu<1$, and suppose $D(S),D(T)\ge\mu$. For any $u\ge0$ such that every $x\in S,y\in T$ has Hamming distance at least $u$,
--   $$
--   u^2\le400n\ln(1/\mu)\,2^{3t}.
--   $$
--   For positive set distance this is equivalently $t\ge\frac13\log_2(\operatorname{dist}(S,T)^2/(400n\ln(1/\mu)))$.
--
--   This is the quantitative circuit-depth obstruction for well-spread output distributions. The exponential formulation also covers overlapping sets without taking the logarithm of zero; the original circuit's workspace is unrestricted.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Fact 4: depth lower bound for well-spread distributions, PDF p. 5. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS

































/-- Fact 4, PDF p.5 and Appendix A p.9, in equivalent exponential form.
Any nonnegative lower bound u on the set distance may be used; no workspace cap is assumed. -/
theorem wellSpreadDepth {n : ℕ} (hn : 0 < n) (P : NLTS.LayeredPreparationCircuit n)
    (S T : Finset (NLTSWord n)) (mu u : ℝ) (hmu : 0 < mu) (hmu1 : mu < 1)
    (hu : 0 ≤ u) (hsep : ∀ x ∈ S, ∀ y ∈ T, u ≤ (hammingDist x y : ℝ))
    (hS : mu ≤ nltsMass (NLTS.preparationOutputDensity P) false S)
    (hT : mu ≤ nltsMass (NLTS.preparationOutputDensity P) false T) :
    u^2 ≤ 400*n*Real.log (1/mu)*(2 : ℝ)^(3*NLTS.preparationDepth P) := by sorry



end QAlgorithms.Papers.Independent.Independent1.P05
