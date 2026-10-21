-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P07_lemma4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P07.lemma4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:10:37.142227+00:00
-- url     : https://prove2.me/theorems/64123034-16d1-41d2-bd9c-405d1e7c0e93
-- title:
--   Disturbance of a projection-and-replacement channel with arbitrary ancilla
-- statement:
--   Let $A,B$ be arbitrary separable complex quantum systems. Let $P$ be any orthogonal projector on $A$, let $\tau$ be any normalized state on $A$, and define the channel $\Pi(X)=PXP+\operatorname{Tr}[(I_A-P)X]\tau$ on all trace-class operators. For every normalized bipartite state $\omega_{AB}$, put $r=\operatorname{Tr}[(I_A-P)\omega_A]$. Then
--
--   $$\|\omega_{AB}-(\Pi\otimes\operatorname{Id}_B)(\omega_{AB})\|_1\le2r+2\sqrt r.$$
--
--   This is a bound on the full trace norm. The replacement state has no support restriction, and both the zero and identity projectors are allowed.
--
--   **Formalization Note** Countable orthonormal-basis labels represent complete separable Hilbert spaces. The nuclear norm is represented as an extended nonnegative infimum, preserving infinity outside its finite domain.
-- source:
--   Uniform finite-dimensional approximation of basic capacities of energy-constrained channels, arXiv:1707.05641v2, PDF p. 16, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07

noncomputable section

open Filter

open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P07

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

/-- Lemma 4, PDF p.16: FULL trace norm, arbitrary ancillary system and arbitrary
replacement state. Both P=0 and P=I are allowed. The real r is the actual
probability Tr((I-P)omega_A), which lies in [0,1] by the state/projector data. -/
theorem lemma4 {I J : Type} [Countable I] [Countable J]
    (P : Hilbert I →L[ℂ] Hilbert I)
    (hself : P.adjoint = P) (hproj : P.comp P = P)
    (tau : Coeff.State I) (omega : Coeff.State (I × J)) :
    let r := (weightedTrace (1 - P) (Coeff.partialRight omega.coefficients)).re
    Coeff.traceSize
      (omega.coefficients - Coeff.tensorApply (projectionReplacement P tau)
        omega.coefficients) ≤ ENNReal.ofReal (2 * r + 2 * Real.sqrt r) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P07

end
