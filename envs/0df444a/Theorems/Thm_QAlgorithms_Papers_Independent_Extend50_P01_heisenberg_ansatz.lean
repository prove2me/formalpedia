-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_heisenberg_ansatz
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.heisenberg_ansatz
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:49:28.765896+00:00
-- url     : https://prove2.me/theorems/8fc2673b-03b7-477e-abf6-c3804c02e3ca
-- title:
--   §V Eqs.(102)–(110): isotropic ansatz and parameter reduction
-- statement:
--   Let $N=2k\ge2$ and consider $p\ge0$ layers, each consisting of one shared $Y$ mixer, one even-bond anisotropic Heisenberg block and one odd-bond block. Let $\alpha_m$ be the mixer angle and $\beta_{m,a},\gamma_{m,a}$ the three even/odd anisotropies. Under normalized collective $SU(2)$ twirling, each layer is exactly
--   $$e^{-i\bar\beta_mH_{\rm even}}e^{-i\bar\gamma_mH_{\rm odd}},\qquad \bar\beta_m=\frac{\beta_{m,X}+\beta_{m,Y}+\beta_{m,Z}}3,\quad\bar\gamma_m=\frac{\gamma_{m,X}+\gamma_{m,Y}+\gamma_{m,Z}}3,$$
--   with isotropic bond Hamiltonians; the $Y$ mixer vanishes. The complete products give equal states on the normalized singlet-product input. Every pair of real reduced angles is attainable. There are $2p$ named real coordinates instead of $7p$, without a minimal-dimension assertion.
--
--   **Formalization Note** The repeated whole-block product printed in Eqs.(102),(110) is replaced by the one-block-per-layer construction described in the prose and Eq.(103).
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 18, §V Eqs.(102)–(110): isotropic ansatz and parameter reduction

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

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P01.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P01.su2BorelSpace

local notation "collective" => (fun (n : ℕ) (V : SU2) => QAlgorithms.Papers.Independent.Information100.P69.matrixPower (Subtype.val V) n)

/-- PDF p.18, Eqs.(102)–(110): exact reduction to two average coordinates per layer.
SOURCE CORRECTION: the printed product over i repeats whole even/odd blocks N times; use
one block per layer as specified by the prose and Eq.(103). Original interleaving is not equated. -/
theorem heisenberg_ansatz (k p : ℕ) (hk : 1 ≤ k) (mu : Measure SU2)
    [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu] (theta : Fin p → Fin 7 → ℝ) :
    (∀ j, twirledHeisenbergLayer (2 * k) mu (theta j) =
      isotropicLayer (2 * k) (reduceHeisenberg (theta j) 0) (reduceHeisenberg (theta j) 1)) ∧
    act ((List.ofFn (fun j => twirledHeisenbergLayer (2 * k) mu (theta j))).prod) (singletProduct k) =
      act ((List.ofFn (fun j => isotropicLayer (2 * k)
        (reduceHeisenberg (theta j) 0) (reduceHeisenberg (theta j) 1))).prod) (singletProduct k) ∧
    (∀ b : Fin p → Fin 2 → ℝ, ∃ t : Fin p → Fin 7 → ℝ, ∀ j, reduceHeisenberg (t j) = b j) ∧
    Fintype.card (HeisenbergParameters p false) = 7 * p ∧
    Fintype.card (HeisenbergParameters p true) = 2 * p := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
