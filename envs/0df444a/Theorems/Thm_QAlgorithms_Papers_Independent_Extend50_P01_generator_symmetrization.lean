-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_generator_symmetrization
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.generator_symmetrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:29:37.053454+00:00
-- url     : https://prove2.me/theorems/2e890454-29bb-468a-a935-31786f36844b
-- title:
--   Abstract / §III: generator symmetrization constructs equivariant ansatz circuits
-- statement:
--   Let $S$ be a finite group represented unitarily by $U_s$ on $n$ qubits. Let $G_1,\ldots,G_k$ be Hermitian generators, with arbitrary real angles $\theta_j$. Define $T(G)=|S|^{-1}\sum_s U_sGU_s^\dagger$. Then each $T(G_j)$ is Hermitian, each $e^{-i\theta_jT(G_j)}$ is unitary, and
--   $$[e^{-i\theta_jT(G_j)},U_s]=0,\qquad [e^{-i\theta_kT(G_k)}\cdots e^{-i\theta_1T(G_1)},U_s]=0.$$
--   The ordered product is also unitary. Zero twirls are retained and generate identity gates. This constructs the equivariant counterpart of the complete ansatz, without a universality or resource improvement claim.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 1, Abstract / §III: generator symmetrization constructs equivariant ansatz circuits

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF pp.1,8–10, Eq.(54): equivariant gates and complete ordered ansatz products.
Zero twirls remain in the list. -/
theorem generator_symmetrization {S : Type*} [Group S] [Fintype S]
    (n k : ℕ) (U : S →* Op n) (hU : ∀ s, U s ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (G : Fin k → Op n) (hG : ∀ j, (G j).IsHermitian) (theta : Fin k → ℝ) :
    (∀ j, (finiteTwirl U (G j)).IsHermitian ∧
      evolve (finiteTwirl U (G j)) (theta j) ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧
      ∀ s, Commute (evolve (finiteTwirl U (G j)) (theta j)) (U s)) ∧
    orderedProd (fun j => evolve (finiteTwirl U (G j)) (theta j)) ∈
      Matrix.unitaryGroup (Qubits n) ℂ ∧
    ∀ s, Commute (orderedProd (fun j => evolve (finiteTwirl U (G j)) (theta j))) (U s) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
