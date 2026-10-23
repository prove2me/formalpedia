-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_genericGramConservation
-- name    : QAlgorithms.Papers.Independent.Information100.P44.genericGramConservation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:32:01.40499+00:00
-- url     : https://prove2.me/theorems/48d72819-2f67-4b81-b01f-1d65c6fa2729
-- title:
--   Corollary 1: generic Gram conservation
-- statement:
--   In the finite Kraus representation $\Phi(X)=\sum_aK_aXK_a^\dagger$, write $v_{r|i}=((K_a)_{ri})_a$ and let $\gamma=\operatorname{diag}(\gamma_i)$ be a diagonal density matrix. The following implications are separate:
--   $$\Phi\text{ trace preserving}\ \Longrightarrow\ \sum_r\langle v_{r|j},v_{r|i}\rangle=\delta_{ij},$$
--   $$\Phi(\gamma)=\gamma\ \Longrightarrow\ \sum_i\gamma_i\langle v_{s|i},v_{r|i}\rangle=\gamma_r\delta_{rs}.$$
--   The Gibbs-type identity does not assume trace preservation, and the trace identity does not assume preservation of $\gamma$. These are conservation laws for unnormalized Gram vectors.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 6, Corollary 1: generic Gram conservation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Corollary 1: the TP and diagonal-preservation implications are independent. -/
theorem genericGramConservation {d n : ℕ} (hd : 0 < d) (K : Fin n → Mat d)
    (gamma : Fin d → ℝ) (hgamma : ∀ i, 0 ≤ gamma i) (hsum : ∑ i, gamma i = 1) :
    (IsTracePreserving (krausApply K) → ∀ i j,
      (∑ r, inner ℂ (krausVector K r j) (krausVector K r i)) =
        if i = j then 1 else 0) ∧
    (krausApply K (Matrix.diagonal fun i => (gamma i : ℂ)) =
        Matrix.diagonal (fun i => (gamma i : ℂ)) → ∀ r s,
      (∑ i, (gamma i : ℂ) * inner ℂ (krausVector K s i) (krausVector K r i)) =
        if r = s then (gamma r : ℂ) else 0) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
