-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_gibbsPolygonObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P44.gibbsPolygonObstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:38:07.896146+00:00
-- url     : https://prove2.me/theorems/65e81b2b-8668-4b68-97f2-214f2f402144
-- title:
--   Corollary 4: Gibbs-weighted polygon obstruction
-- statement:
--   Let $\Phi$ be completely positive on a nonzero finite system and preserve the full-rank diagonal density matrix $\gamma=\operatorname{diag}(\gamma_i)$, where $\gamma_i>0$ and $\sum_i\gamma_i=1$. For output labels $r\ne s$, set $q_i=\gamma_i\Phi(|i\rangle\langle i|)_{rs}$ and $b_i=\gamma_i\sqrt{p(r|i)p(s|i)}$. Then
--   $$|q_i|\le b_i,\qquad \sum_iq_i=0.$$
--   If $b_{i_0}>\sum_{i\ne i_0}b_i$ for some input label, no CP map preserving $\gamma$ and having the same transition probabilities saturates every elementary bound $|\Phi(|i\rangle\langle i|)_{rs}|\le\sqrt{p(r|i)p(s|i)}$. Trace preservation is not assumed. The obstruction therefore covers CGP and thermal maps when $\gamma$ is their Gibbs state.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 14, Corollary 4: Gibbs-weighted polygon obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.14, Corollary 4: weighted bounds and the obstruction for all CP preserving maps,
including trace-changing maps. CGP and TO are subclasses. -/
theorem gibbsPolygonObstruction {d : ℕ} (hd : 0 < d) (gamma : Fin d → ℝ)
    (hgamma : ∀ i, 0 < gamma i) (hsum : ∑ i, gamma i = 1)
    (Phi : Mat d →ₗ[ℂ] Mat d) (hcp : QAlgorithms.Entanglement.IsCompletelyPositive Phi)
    (hpres : Phi (Matrix.diagonal fun i => (gamma i : ℂ)) =
      Matrix.diagonal (fun i => (gamma i : ℂ))) (r s : Fin d) (hrs : r ≠ s) :
    (∀ i, ‖(gamma i : ℂ) * Phi (matrixUnit i i) r s‖ ≤
      gamma i * Real.sqrt (population Phi r i * population Phi s i)) ∧
    (∑ i, (gamma i : ℂ) * Phi (matrixUnit i i) r s) = 0 ∧
    (∀ i0, (∑ i ∈ Finset.univ.erase i0,
        gamma i * Real.sqrt (population Phi r i * population Phi s i)) <
      gamma i0 * Real.sqrt (population Phi r i0 * population Phi s i0) →
      ¬ ∃ Psi : Mat d →ₗ[ℂ] Mat d, QAlgorithms.Entanglement.IsCompletelyPositive Psi ∧
        Psi (Matrix.diagonal fun i => (gamma i : ℂ)) =
          Matrix.diagonal (fun i => (gamma i : ℂ)) ∧
        (∀ t i, population Psi t i = population Phi t i) ∧
        ∀ i, ‖Psi (matrixUnit i i) r s‖ =
          Real.sqrt (population Phi r i * population Phi s i)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
