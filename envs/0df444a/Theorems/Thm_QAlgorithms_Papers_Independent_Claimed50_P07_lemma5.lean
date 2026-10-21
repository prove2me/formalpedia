-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P07_lemma5
-- name    : QAlgorithms.Papers.Independent.Claimed50.P07.lemma5
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:11:22.874345+00:00
-- url     : https://prove2.me/theorems/bddd04eb-e504-4ddc-8aa4-0d8d07b6ebdd
-- title:
--   Spectral truncation tail bound, with the zero-gap case retained
-- statement:
--   Let $H_A$ be a positive self-adjoint Hamiltonian with complete ordered eigenbasis $(\tau_k)_{k\ge0}$ and eigenvalues $E_k^A$ counted with multiplicity, tending to infinity. Let $m\ge1$, and let $P_m$ project onto $\tau_0,\ldots,\tau_{m-1}$. Suppose $\rho$ is a normalized trace-class state with $\operatorname{Tr}H_A\rho\le E<\infty$ and $E\ge E_0^A$. Write $r_m=\operatorname{Tr}[(I_A-P_m)\rho]$ and $D_m=E_m^A-E_0^A$. Then
--
--   $$D_m r_m\le E-E_0^A,\qquad D_m>0\ \Longrightarrow\ r_m\le\frac{E-E_0^A}{D_m}.$$
--
--   This controls the mass outside the low-energy subspace and retains degenerate ground eigenspaces.
--
--   **Formalization Note** The source prints the quotient without a zero-gap qualification. The division-free inequality is valid even if $D_m=0$; the quotient is asserted only for $D_m>0$. The extended mean energy retains infinity.
-- source:
--   Uniform finite-dimensional approximation of basic capacities of energy-constrained channels, arXiv:1707.05641v2, PDF p. 16, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P07

noncomputable section

open Filter

open scoped NNReal ENNReal BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P07

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier30.P05 (EnergySpectrum groundEnergy)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 5, PDF p.16, with the ground-degeneracy correction made explicit.
Printed: tail <= (E-E0)/(E_m-E0). Changed: assert the division-free inequality
for every m>0, and the printed quotient only if E_m>E0. Why: a repeated
lowest eigenvalue makes the printed denominator zero; no simple-ground-state
assumption is present in the source. The mean energy is extended nonnegative,
so infinite-energy states cannot satisfy the finite budget hypothesis. -/
theorem lemma5 (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (rho : TC.State b) (E : ℝ) (m : ℕ) (hm : 0 < m)
    (henergy : TC.spectralEnergy b S.levels rho ≤ ENNReal.ofReal E)
    (hbudget : groundEnergy S ≤ E) :
    ((S.levels m : ℝ) - groundEnergy S) * truncationTail b rho m ≤
        E - groundEnergy S ∧
    (0 < (S.levels m : ℝ) - groundEnergy S →
      truncationTail b rho m ≤
        (E - groundEnergy S) / ((S.levels m : ℝ) - groundEnergy S)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P07

end
