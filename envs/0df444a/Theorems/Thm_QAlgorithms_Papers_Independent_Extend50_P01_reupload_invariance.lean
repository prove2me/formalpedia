-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_reupload_invariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.reupload_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:43:16.167235+00:00
-- url     : https://prove2.me/theorems/45f1742a-2617-4ee4-9838-00b816fab7a6
-- title:
--   §IV Eqs.(68)–(87): invariant re-uploading blueprint
-- statement:
--   Let a group $S$ act on data $x\in\mathcal X$, with a unitary representation $U_s$ on $n$ qubits. Let $E(x)$ be a unitary embedding with $E(sx)=U_sE(x)U_s^\dagger$. For arbitrary parameters $\theta$, choose data-independent unitary blocks $W_0(\theta),\ldots,W_L(\theta)$ commuting with every $U_s$, where $L\ge0$. Let $\psi_0$ be a unit vector fixed exactly by every $U_s$, and $O$ a Hermitian observable with $U_sOU_s^\dagger=O$. Put $C(\theta,x)=W_LE(x)\cdots W_1E(x)W_0$, $\psi=C\psi_0$, and $y=\operatorname{Re}\langle\psi,O\psi\rangle$. Then
--   $$C(\theta,sx)=U_sC(\theta,x)U_s^\dagger,\quad\psi(\theta,sx)=U_s\psi(\theta,x),\quad y(\theta,sx)=y(\theta,x).$$
--   The conjugation channels of each $W_j$ also commute with the symmetry conjugation on every operator. These are sufficient conditions for invariant re-uploading predictions.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 20, §IV Eqs.(68)–(87): invariant re-uploading blueprint

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

/-- PDF pp.10–11, Eqs.(68)–(87), recap p.20: sufficient conditions for all parameters and
inputs. The state is exactly fixed and normalized, and the observable is Hermitian. -/
theorem reupload_invariance {S X Theta : Type*} [Group S] [MulAction S X]
    (n L : ℕ) (U : S →* Op n) (hU : ∀ s, U s ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (E : X → Op n) (hE : ∀ x, E x ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hequiv : ∀ s x, E (s • x) = conjugate (U s) (E x))
    (W : Theta → Fin (L + 1) → Op n)
    (hW : ∀ theta j, W theta j ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hcomm : ∀ theta j s, Commute (W theta j) (U s))
    (psi0 : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi0)
    (hfixed : ∀ s, act (U s) psi0 = psi0)
    (O : Op n) (hO : O.IsHermitian) (hinv : ∀ s, conjugate (U s) O = O) :
    (∀ theta x s,
      reupload (E (s • x)) (List.ofFn (W theta)) = conjugate (U s) (reupload (E x) (List.ofFn (W theta))) ∧
      act (reupload (E (s • x)) (List.ofFn (W theta))) psi0 =
        act (U s) (act (reupload (E x) (List.ofFn (W theta))) psi0) ∧
      expectation O (act (reupload (E (s • x)) (List.ofFn (W theta))) psi0) =
        expectation O (act (reupload (E x) (List.ofFn (W theta))) psi0)) ∧
    (∀ theta j s rho, conjugate (W theta j) (conjugate (U s) rho) =
      conjugate (U s) (conjugate (W theta j) rho)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
