-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_interaction_strength
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.interaction_strength
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:59:11.808685+00:00
-- url     : https://prove2.me/theorems/94e8c45f-7d0f-4d52-bd80-b857a8ec393d
-- title:
--   Detecting the maximum n-body interaction strength
-- statement:
--   Let 1≤k<n and T>0. Suppose an integrable invariant Hermitian Hamiltonian on n qubits has the form H(t)=H_0(t)+γ(t)Z^{⊗n}, where H_0(t) is a sum of k-local terms and |γ| attains a maximum on [0,T], as presupposed by the source’s maximum notation. Let V be its propagator from the identity. There exists t_max∈[0,T] attaining the maximum of |γ|, and
--
--   $$\frac{|\Phi_n(V(T))_{\mathrm{principal}}|}{2^nT}\le |\gamma(t_{\max})|=\max_{0\le t\le T}|\gamma(t)|.$$
--
--   Thus the measured principal n-body phase bounds the peak interaction strength without individually symmetric summands in H_0.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 4, II.C Eq.(5): detecting an n-body interaction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.4, Eq.5: the source uses an attained maximum of |gamma|.
Its existence is explicit; continuity is not required. The absolute value is
present in the original PDF. H0's local summands need not individually preserve U(1). -/
theorem interaction_strength (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (T : ℝ) (hT : 0 < T) (H0 H V : ℝ → QMat n) (gamma : ℝ → ℝ)
    (hPath : Propagator H V T) (hSym : ∀ t ∈ Set.Icc 0 T, U1Invariant (H t))
    (hLocal : ∀ t ∈ Set.Icc 0 T, H0 t ∈ localTermSpan k)
    (hForm : ∀ t ∈ Set.Icc 0 T, H t = H0 t + (gamma t : ℂ) • initialString n n)
    (hMax : ∃ tmax ∈ Set.Icc 0 T,
      ∀ t ∈ Set.Icc 0 T, |gamma t| ≤ |gamma tmax|) :
    ∃ tmax ∈ Set.Icc 0 T,
      (∀ t ∈ Set.Icc 0 T, |gamma t| ≤ |gamma tmax|) ∧
      |(u1BodyPhase (V T) n).toReal| / ((2 : ℝ)^n*T) ≤ |gamma tmax| := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
