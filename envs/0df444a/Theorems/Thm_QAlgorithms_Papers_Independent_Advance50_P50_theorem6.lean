-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_theorem6
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.theorem6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:14:16.271989+00:00
-- url     : https://prove2.me/theorems/63d01bfb-7455-4d6c-8b62-9d10a271c295
-- title:
--   Theorem 6: no informative one-copy local-unitary model
-- statement:
--   An $n$-qubit input $\rho$ is a positive semidefinite, trace-one matrix on the fixed computational basis, of dimension $d=2^n$. A $k$-copy model has a fixed input-independent unitary $U$, a Hermitian observable $O$, effective observable $\widetilde O=U^\dagger O U$, and exact response $h(\rho)=\operatorname{Tr}[U\rho^{\otimes k}U^\dagger O]$. Let $L=\bigotimes_{j=1}^n U(2)$ denote the represented local unitary group. Fix $n\ge2$ and a local-unitary-invariant pure-state measure $E$ valued in $[0,1]$, with $E=0$ exactly on fully product pure states. Fix $0<b\le1$ with both $E=0$ and $E=b$ classes nonempty, and let $R$ be their pure-state union. For a one-copy model,
--
--   $$h\text{ locally unitary invariant on }R\quad\Longrightarrow\quad h(\rho)=\frac{\operatorname{Tr}O}{2^n}\quad(\rho\in R).$$
--
--   Consequently the model provides no class information. The conclusion uses the averaging statement (32), with no assumption that the local Lie-algebra complement is trivial.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 12, Theorem 6: no informative one-copy local-unitary model

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

/-- PDF pp.12–13, Theorem 6, Eq.(32): all invariant one-copy models are
constant on the pure entanglement dataset. No use is made of the false Eq.(31). -/
theorem theorem6 {n : ℕ} (hn : 2 ≤ n) (E : EntanglementMeasure n)
    (b : ℝ) (hb : 0 < b ∧ b ≤ 1)
    (hzero : ∃ rho, IsPure rho ∧ E.value rho = 0)
    (hpositive : ∃ rho, IsPure rho ∧ E.value rho = b)
    (M : ExpectationModel (Qubits n) 1)
    (hinv : DomainInvariant (localUnitaryMatrices n) (entanglementDomain E b) M.response) :
    ∀ rho ∈ entanglementDomain E b,
      M.response rho = M.observable.trace.re / (2 : ℝ) ^ n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
