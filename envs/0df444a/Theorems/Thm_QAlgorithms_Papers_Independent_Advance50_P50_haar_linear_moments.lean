-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_haar_linear_moments
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.haar_linear_moments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:28:48.422323+00:00
-- url     : https://prove2.me/theorems/1d58d7bd-69c8-43c4-b846-99d7e704f0ed
-- title:
--   Appendix F.1: exact Haar moments before the erroneous specialization
-- statement:
--   Fix $n\ge1$, $d=2^n$, a real density matrix $\rho_{\rm in}$, and a Hermitian purely imaginary matrix $O$. Let $V$ have the canonical normalized Haar law on $U(d)$ and $X(V)=\operatorname{Tr}[O V\rho_{\rm in}V^\dagger]$. Then $X$ and $X^2$ are integrable and
--
--   $$\mathbb E X=\frac{\operatorname{Tr}O}{d}=0,$$
--
--   $$\operatorname{Var}X=\mathbb E X^2=\frac{\operatorname{Tr}(O^2)\operatorname{Tr}(\rho_{\rm in}^2)}{d^2-1}-\frac{\operatorname{Tr}(O^2)}{d(d^2-1)}.$$
--
--   This retains the coherent first equality of Eq.(F5); it makes no normalization assumption on $\operatorname{Tr}(O^2)$ and does not adopt its erroneous Pauli specialization.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 28, Appendix F.1: exact Haar moments before the erroneous specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.27–28, Eqs.(F4) and the first equality of (F5): exact Haar moments
for fixed real fiduciary density and imaginary Hermitian observable. The
contradictory final Pauli substitution in (F5) is deferred separately. -/
theorem haar_linear_moments {n : ℕ} (hn : 1 ≤ n)
    (rho O : Mat (Qubits n)) (hrho : IsDensityMatrix rho)
    (hreal : ∀ x y, (rho x y).im = 0) (hO : O.IsHermitian)
    (himaginary : ∀ x y, (O x y).re = 0) :
    let mu := QAlgorithms.Schur.unitaryHaar (2 ^ n)
    let X := haarOutput n rho O
    Integrable X mu ∧ Integrable (fun u => (X u) ^ 2) mu ∧
    (∫ u, X u ∂mu) = O.trace.re / (2 : ℝ) ^ n ∧
    O.trace.re / (2 : ℝ) ^ n = 0 ∧
    variance X mu = (∫ u, (X u) ^ 2 ∂mu) ∧
    variance X mu = (O * O).trace.re * purity rho / (((2 : ℝ) ^ n) ^ 2 - 1) -
      (O * O).trace.re / ((2 : ℝ) ^ n * (((2 : ℝ) ^ n) ^ 2 - 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
