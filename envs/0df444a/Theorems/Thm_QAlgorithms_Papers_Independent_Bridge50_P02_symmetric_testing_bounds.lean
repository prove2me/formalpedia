-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_symmetric_testing_bounds
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.symmetric_testing_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:42:38.131207+00:00
-- url     : https://prove2.me/theorems/0fe15b41-d45d-46a1-b571-2396eb35cf5b
-- title:
--   Lemma 2: two-sided symmetric testing bounds
-- statement:
--   Let $A,B$ be strictly positive operators on a nonzero finite-dimensional complex Hilbert space, with arbitrary positive traces. Set $\Delta(X)=AXB^{-1}$ and $\Omega_B=B^{1/2}$ in Hilbert–Schmidt space. Let $e^*_{\rm sym}(A,B)$ be the infimum, over all effects $T$, of $\operatorname{Tr}(A(I-T))+\operatorname{Tr}(BT)$. For every $s\in[0,1]$,
--   $$\langle\Omega_B,\Delta(1+\Delta)^{-1}\Omega_B\rangle\le e^*_{\rm sym}(A,B)\le\langle\Omega_B,\Delta^s\Omega_B\rangle=\operatorname{Tr}(A^sB^{1-s}).$$
--   Writing $P_\lambda(A),P_\mu(B)$ for the spectral projections, the lower quadratic form equals
--   $$\sum_{\lambda\in\operatorname{sp}A,\,\mu\in\operatorname{sp}B}\frac{\lambda/\mu}{1+\lambda/\mu}\operatorname{Tr}(BP_\lambda(A)P_\mu(B)).$$
--   If $\mu_{A\mid B}$ is the finite spectral measure of $-\log\Delta$ in $\Omega_B$, these forms are respectively $\int(1+e^x)^{-1}\,d\mu_{A\mid B}(x)$ and $\int e^{-sx}\,d\mu_{A\mid B}(x)$.
--
--   The measure has mass $\operatorname{Tr}B$. No trace-one normalization or factor $1/2$ is imposed.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 13, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Lemma 2, PDF p.13, (3.11)--(3.12): arbitrary strictly positive traces, ALL effects,
and the finite spectral-measure interpretation. -/
theorem symmetric_testing_bounds [Nonempty I] (A B : Mat I)
    (hA : A.PosDef) (hB : B.PosDef) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    resolventOverlap A B ≤ symmetricError A B ∧
    symmetricError A B ≤ modularQuadratic B (positiveMatrixRpow (modularMatrix A B) s) ∧
    modularQuadratic B (positiveMatrixRpow (modularMatrix A B) s) = petzOverlap A B s ∧
    resolventOverlap A B =
      (∑ l ∈ eigenvalueSet A hA.isHermitian, ∑ m ∈ eigenvalueSet B hB.isHermitian,
        ((l/m)/(1+l/m)) * evaluate B (eigenprojector A l * eigenprojector B m)) ∧
    spectralIntegral A B (fun x => 1/(1+Real.exp x)) = resolventOverlap A B ∧
    spectralIntegral A B (fun x => Real.exp (-s*x)) = petzOverlap A B s := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
