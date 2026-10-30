-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_tfim_qaoa_symmetrization
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.tfim_qaoa_symmetrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:47:04.104188+00:00
-- url     : https://prove2.me/theorems/eef20fd9-df4d-4a31-a861-298574e49e34
-- title:
--   §V Eqs.(97)–(98): parity twirling removes the extra Y mixer
-- statement:
--   On a positive-length periodic chain, let $P=\bigotimes_iX_i$ and $T_P(A)=(A+PAP)/2$. For every site,
--   $$T_P(Y_i)=0,\qquad T_P(X_i)=X_i,\qquad T_P(Z_iZ_{i+1})=Z_iZ_{i+1}.$$
--   For any $p\ge0$ layers and real shared parameters $\alpha_m,\beta_m,\gamma_m$, replacing the generators in the source's QAOA-prime product by their twirls therefore gives exactly the standard QAOA matrix product and its state on $|+\rangle^{\otimes N}$, with $\beta_m,\gamma_m$ unchanged. Exponents have no half-angle factor. This is a generator and ansatz identity, without an optimizer or exact-recovery claim.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 17, §V Eqs.(97)–(98): parity twirling removes the extra Y mixer

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

local notation "parity" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P69.matrixPower pauliX n)

/-- PDF p.17, Eqs.(97),(98): twirling deletes exactly the Y mixer, preserving beta and gamma. -/
theorem tfim_qaoa_symmetrization (N p : ℕ) (hN : 1 ≤ N)
    (alpha beta gamma : Fin p → ℝ) :
    (∀ i : Fin N, involutionTwirl (parity N) (onWire i pauliY) = 0 ∧
      involutionTwirl (parity N) (onWire i pauliX) = onWire i pauliX ∧
      involutionTwirl (parity N) (onWire i pauliZ * onWire (nextSite i) pauliZ) =
        onWire i pauliZ * onWire (nextSite i) pauliZ) ∧
    twirledQaoa alpha beta gamma = (qaoa beta gamma : Op N) ∧
    act (twirledQaoa (n := N) alpha beta gamma) (plusState N) = act (qaoa beta gamma) (plusState N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
