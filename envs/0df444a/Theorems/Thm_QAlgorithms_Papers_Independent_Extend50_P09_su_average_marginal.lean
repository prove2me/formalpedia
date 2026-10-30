-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_su_average_marginal
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.su_average_marginal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:45:17.466964+00:00
-- url     : https://prove2.me/theorems/d165e6fb-f411-4a0c-ad38-87e1efc59e01
-- title:
--   Appendix D: symmetric-code average and t-qudit marginal
-- statement:
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   For this exact average identity let the normalized logical input be any pure $\rho=|v\rangle\langle v|$ and retain any first $t$ sites, $1\le t\le n$. Put $\omega_\lambda=\Pi_\lambda/(l_\lambda r_\lambda)$, the actual normalized isotypic projector. The full averaged encoded state equals the average obtained by replacing the ancillary state with $\omega_\lambda$, and
--   $$\operatorname{Tr}_{n-t}\Psi_{\rm avg}=\frac1n\sum_{j=1}^t\rho^{(j)}\otimes\left(\operatorname{Tr}_{n-t}\omega_\lambda\right)^{(\bar j)}
--   +\begin{cases}\dfrac{n-t}{n}\operatorname{Tr}_{n-t-1}\omega_\lambda,&t<n,\\0,&t=n.\end{cases}$$
--   Here $\bar j$ denotes the other $t-1$ retained positions; the first marginal of $\omega_\lambda$ retains $t-1$ ancilla sites, and the last retains $t$.
--
--   The last term is omitted at $t=n$. This formula makes no multiple-erasure error-performance claim.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 21, Appendix D: symmetric-code average and t-qudit marginal

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix D, PDF pp.21–22, (D9)–(D10): exact average and
arbitrary t retained qudits; no assertion of t>1 recovery performance. -/
theorem su_average_marginal (d n t : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (ht0 : 1 ≤ t) (ht : t ≤ n) (lam : Schur.Partition d (n-1))
    (psi : EuclideanSpace ℂ (Fin (rdim lam))) (hpsi : IsState psi)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v)
    (mu : Measure (Op (CovariantWord d n))) (hmu : IsCommutantHaarLaw (SUGroup d n) mu) :
    (∫ V, appendUnitaryEncoder (show 1 ≤ n by omega) (suAncilla lam psi) V
      (logicalMatrix (pureDensity v)) ∂mu) =
    (∫ V, appendUnitaryEncoder (show 1 ≤ n by omega) (isotypicState lam) V
      (logicalMatrix (pureDensity v)) ∂mu) ∧
    firstTrace ht (∫ V, appendUnitaryEncoder (show 1 ≤ n by omega) (suAncilla lam psi) V
      (logicalMatrix (pureDensity v)) ∂mu) =
      suMarginalFormula hn ht0 ht lam (pureDensity v) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
