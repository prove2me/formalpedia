-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P05_positiveOperatorFidelityLowerBound
-- name    : QAlgorithms.Papers.Independent.Advance50.P05.positiveOperatorFidelityLowerBound
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:28:21.436604+00:00
-- url     : https://prove2.me/theorems/9643e3cd-93da-4f46-a020-754d8c7b7aa8
-- title:
--   Root-fidelity lower bound for arbitrary positive operators
-- statement:
--   Let $P,Q$ be arbitrary positive semidefinite operators on a finite-dimensional Hilbert space. Neither a trace-one condition nor a trace upper bound is assumed. Define root fidelity and the full trace norm by $F(P,Q)=\|\sqrt P\sqrt Q\|_1$ and $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$. Then
--   $$
--   F(P,Q)\ge\frac{\operatorname{Tr}P+\operatorname{Tr}Q}{2}-\frac12\|P-Q\|_1.
--   $$
--   This includes zero operators and operators of unequal or arbitrarily large trace. It supplies the unnormalized fidelity estimate used in decoupling arguments.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, PDF p. 16, Lemma 11, Eq.(62): fidelity bound for arbitrary positive operators

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P05

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P19 (first both epr IsIso)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog marginalAB marginalAC)

open QAlgorithms.Papers.Independent.Support50.P21 (dMin weakPositive PositiveTensorBasis)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Buscemi--Datta, arXiv:1006.1896v2, PDF pp.16--17, Lemma 11, (62).
Arbitrary positive operators with arbitrary traces; no normalization or trace cap.
The trace norm is the full Schatten one-norm and F is root fidelity. -/
theorem positiveOperatorFidelityLowerBound
    {I : Type} [Fintype I] [DecidableEq I]
    (P Q : Matrix I I ℂ) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    rootFidelity P Q ≥ (P.trace.re + Q.trace.re) / 2 - traceNorm (P - Q) / 2 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P05

end
