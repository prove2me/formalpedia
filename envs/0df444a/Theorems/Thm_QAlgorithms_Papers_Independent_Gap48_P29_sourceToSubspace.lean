-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_sourceToSubspace
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.sourceToSubspace
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:25:33.61133+00:00
-- url     : https://prove2.me/theorems/01581bbf-b216-4f11-866d-2f3f10450c41
-- title:
--   Source-specific expurgation into reliable subspaces
-- statement:
--   Let $\Sigma=\{\rho_n\}$ be a source on tensor powers of a fixed nonzero finite-dimensional Hilbert space, satisfying the quantum asymptotic equipartition property (QAEP). Its entropy rate is $s=\limsup_n S(\rho_n)/n$, in bits. No independence or identical-distribution hypothesis is imposed. Let $\mathcal A_n$ be trace-preserving transmission operations satisfying $F_e(\rho_n,\mathcal A_n)\to1$. For every nonnegative rate $R<s$, there are nonzero subspaces $V_n$ of the source block spaces such that
--
--   $$\frac{\log_2\dim V_n}{n}\longrightarrow R,\qquad\min_{\psi\in V_n,\,\|\psi\|=1}\langle\psi|\mathcal A_n(|\psi\rangle\langle\psi|)|\psi\rangle\longrightarrow1.$$
--
--   The retained subspaces depend on the source and its transmission operations. This is the proof's precise all-rates-below-entropy conclusion, using the same operations.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 6, Section V.A, Eqs.(68)–(69), pp.6–8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF pp.6--8, section V.A, especially Eq.(69): every nonnegative rate strictly
below the entropy rate is supported by retained source-space subspaces under the
same operations. Their logarithmic dimension converges to the chosen rate. -/
theorem sourceToSubspace (S : BlockQuantumSource) (hS : QAEP S)
    (A : (n : ℕ) → Superop (SourceRegister S.dimension n) (SourceRegister S.dimension n))
    (hA : ∀ n, IsChannel (A n))
    (hgood : Tendsto (fun n => fe (S.rho n) (A n)) atTop (nhds 1))
    (R : ℝ) (hR : 0 ≤ R) (hRS : R < sourceEntropyRate S) :
    ∃ P : (n : ℕ) → Matrix (SourceRegister S.dimension n) (SourceRegister S.dimension n) ℂ,
      (∀ n, IsProjection (P n) ∧ 0 < projectionDimension (P n)) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (projectionDimension (P n) : ℝ) / n)
        atTop (nhds R) ∧ SubspaceReliable P A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
