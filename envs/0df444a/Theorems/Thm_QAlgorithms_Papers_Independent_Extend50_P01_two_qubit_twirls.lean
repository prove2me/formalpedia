-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_two_qubit_twirls
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.two_qubit_twirls
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:41:11.2347+00:00
-- url     : https://prove2.me/theorems/d56ec0de-4c3a-458b-ab7e-846596611a71
-- title:
--   §III Eqs.(55)–(67): explicit exchange and sign symmetrizations
-- statement:
--   On two qubits let $\mathcal G=\{X_1,Y_1,Z_1,X_2,Y_2,Z_2,Z_1Z_2\}$. Write $T_\leftrightarrow$ for the normalized SWAP twirl, $T_\pm$ for the normalized $X_1X_2$ twirl, and $T_K$ for the full Klein-four twirl. For each $A\in\{X,Y,Z\}$, $T_\leftrightarrow(A_1)=T_\leftrightarrow(A_2)=(A_1+A_2)/2$, while $Z_1Z_2$ is fixed. The sign twirl fixes exactly $X_1,X_2,Z_1Z_2$ within this input set and kills its other generators. For every operator $B$,
--   $$T_\leftrightarrow T_\pm(B)=T_\pm T_\leftrightarrow(B)=T_K(B),\qquad T_K[\mathcal G]\setminus\{0\}=\{(X_1+X_2)/2,Z_1Z_2\}.$$
--   This gives the exact normalized generator mappings, including the suppressed zero values.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 9, §III Eqs.(55)–(67): explicit exchange and sign symmetrizations

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

/-- PDF pp.8–9, Eqs.(55)–(67): normalized per-generator mappings and nonzero image.
The printed sets suppress zero generators, so literal image equality would be wrong. -/
theorem two_qubit_twirls :
    (∀ a : Fin 3,
      involutionTwirl swapGate (axis a ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
        (1 / 2 : ℂ) • (axis a ⊗ₖ (1 : Matrix Bool Bool ℂ) + (1 : Matrix Bool Bool ℂ) ⊗ₖ axis a) ∧
      involutionTwirl swapGate ((1 : Matrix Bool Bool ℂ) ⊗ₖ axis a) =
        (1 / 2 : ℂ) • (axis a ⊗ₖ (1 : Matrix Bool Bool ℂ) + (1 : Matrix Bool Bool ℂ) ⊗ₖ axis a)) ∧
    involutionTwirl swapGate (pauliZ ⊗ₖ pauliZ) = pauliZ ⊗ₖ pauliZ ∧
    (∀ A ∈ twoGateSet, involutionTwirl (pauliX ⊗ₖ pauliX) A =
      if A ∈ ({pauliX ⊗ₖ (1 : Matrix Bool Bool ℂ), (1 : Matrix Bool Bool ℂ) ⊗ₖ pauliX,
        pauliZ ⊗ₖ pauliZ} : Set _) then A else 0) ∧
    (∀ A, involutionTwirl swapGate (involutionTwirl (pauliX ⊗ₖ pauliX) A) = finiteTwirl kleinMatrix A ∧
      involutionTwirl (pauliX ⊗ₖ pauliX) (involutionTwirl swapGate A) = finiteTwirl kleinMatrix A) ∧
    (finiteTwirl kleinMatrix '' twoGateSet) \ {0} =
      {(1 / 2 : ℂ) • (pauliX ⊗ₖ (1 : Matrix Bool Bool ℂ) + (1 : Matrix Bool Bool ℂ) ⊗ₖ pauliX),
        pauliZ ⊗ₖ pauliZ} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
