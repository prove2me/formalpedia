-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_dense_coding_transitions
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.dense_coding_transitions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:32:27.5724+00:00
-- url     : https://prove2.me/theorems/1dfea13f-9486-4bc5-bcba-c1e3cb49b71d
-- title:
--   Symmetric Bell-resource dense-coding transitions
-- statement:
--   Let $N\ge2$ and $d\ge2$. Use the Bell resource and completed SRM effects $\widehat\Pi_i=\Pi_i+\Delta/N$. Entanglement transfer constructs the remote state $\widetilde\chi_i=\widehat\Pi_i^T/d^{N+1}$ on all Bob ports and reference $D$. These effects are symmetric, $p_i=\operatorname{Tr}\widetilde\chi_i=1/N$, and $\chi_i=\widetilde\chi_i/p_i$ is a density matrix. Let $F_{i|k}$ be its overlap with the normalized Bell projector on $B_kD$, extended by identity elsewhere. The transition coefficients $q_{i|k}=d^2p_iF_{i|k}$ sum to one for every $k$. The diagonal value is the corresponding deterministic entanglement fidelity $F$ and all off-diagonal values equal $F_e$, where
--
--   $$F+(N-1)F_e=\frac N{d^2},\qquad F_e=\frac{N}{d^2(N-1)}-\frac F{N-1}.$$
--
--   This is a transition-law identity for the specified symmetric construction; it asserts no information optimum.
--
--   At each fixed $d\ge2$, the common off-diagonal fidelity also satisfies $F_e\to1/d^2$ as $N\to\infty$. The sequence is represented by the displayed expression for $F_e$, which equals the actual off-diagonal value for every $N\ge2$.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 17, §VI, Eqs.(67)–(74): dense-coding transition fidelities for the symmetric Bell-resource construction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- §VI, PDF pp.17–18 Eqs.(67)–(74): the concrete real completed-SRM
Bell-resource construction, including the off-diagonal limit F_e → 1/d² at
fixed d. N≥2 guards the finite identity; the limit ignores n=0,1 defaults. -/
theorem dense_coding_transitions (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    (∀ i : Fin N,
      (completedEffects d N (some i))ᵀ = completedEffects d N (some i) ∧
      denseProbability d N i = (N : ℝ)⁻¹ ∧
      IsDensityMatrix (denseState d N i) ∧
      denseFidelity d N i i = QuditFidelity.entanglementFidelity d (by omega)
        (successfulMap (1 : AliceMatrix d N) (completedEffects d N))) ∧
    (∀ k : Fin N, (∑ i : Fin N, denseTransition d N i k) = 1) ∧
    (∃ Fe : ℝ, (∀ i k : Fin N, i ≠ k → denseFidelity d N i k = Fe) ∧
      QuditFidelity.entanglementFidelity d (by omega)
        (successfulMap (1 : AliceMatrix d N) (completedEffects d N)) + ((N : ℝ) - 1) * Fe =
          (N : ℝ) / (d : ℝ) ^ 2 ∧
      Fe = (N : ℝ) / ((d : ℝ) ^ 2 * ((N : ℝ) - 1)) -
        QuditFidelity.entanglementFidelity d (by omega)
          (successfulMap (1 : AliceMatrix d N) (completedEffects d N)) / ((N : ℝ) - 1)) ∧
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) / ((d : ℝ) ^ 2 * ((n : ℝ) - 1)) -
        QuditFidelity.entanglementFidelity d (by omega)
          (successfulMap (1 : AliceMatrix d n) (completedEffects d n)) / ((n : ℝ) - 1))
      Filter.atTop (nhds (1 / (d : ℝ) ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
