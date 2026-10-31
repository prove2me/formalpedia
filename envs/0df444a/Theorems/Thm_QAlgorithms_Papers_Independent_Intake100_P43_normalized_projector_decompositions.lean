-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P43_normalized_projector_decompositions
-- name    : QAlgorithms.Papers.Independent.Intake100.P43.normalized_projector_decompositions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:33:11.769502+00:00
-- url     : https://prove2.me/theorems/ba5df90d-605a-48da-96a9-c42994c194ff
-- title:
--   Normalized projector decompositions have high-rank components
-- statement:
--   Fix local computational bases of $H=\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, where $1\le d_A\le d_B$, and an integer $1\le r\le d_A$. All subspaces and dimensions are complex. Write $\operatorname{Sch}(v)$ for the rank of the coefficient matrix of $v$. Subspace rank conditions concern every nonzero vector and do not require unit norm. Let $S$ have the maximum dimension $N=(d_A-r+1)(d_B-r+1)$ and lower Schmidt rank $r$, and set $\rho=P_S/N$, where $P_S$ is the canonical orthogonal projector. This is a density matrix admitting pure-state ensembles. In every finite or countable decomposition $\rho=\sum_i p_i|v_i\rangle\langle v_i|$, with unit $v_i$, nonnegative weights of sum one, and convergent entry sums,
--
--   $$p_i>0\ \Longrightarrow\ v_i\in S\ \text{and}\ \operatorname{Sch}(v_i)\ge r.$$
--
--   Hence the mixed-state Schmidt measure (the least achievable maximum rank over positive-weight ensemble terms) is at least $r$. The average-rank series is summable and $\sum_i p_i\operatorname{Sch}(v_i)\ge r$ for every ensemble, giving the corresponding average-rank convex-roof lower bound. Zero-weight terms are unconstrained by membership in $S$. This states the operational rank content of the application.
-- source:
--   On the dimension of subspaces with bounded Schmidt rank, arXiv:0706.0705v1, PDF p. 4, Discussion, normalized projector application

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-- PDF p.4, projector-decomposition application: construct rho from S;
positive-weight pure components lie in S and have rank at least r. This yields
both the max-component Schmidt measure bound and the average-rank bound.
A finite decomposition witness uses the imported accepted PureEnsemble; the
universal assertion ranges over all countable decompositions explicitly.
Zero-weight terms need not lie in S. No arbitrary entanglement functional is
claimed to obey the numerical lower bound r. -/
theorem normalized_projector_decompositions (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (S : Submodule ℂ (Bipartite dA dB)) (hS : HasLowerSchmidtRank S r)
    (hdim : Module.finrank ℂ S = (dA - r + 1) * (dB - r + 1)) :
    QAlgorithms.IsDensityMatrix (normalizedProjector S) ∧
    (∃ E : PureEnsemble (Fin dA × Fin dB),
      QAlgorithms.ensembleDensity E.weight E.vector = normalizedProjector S) ∧
    r ≤ schmidtMeasure (normalizedProjector S) ∧
    ∀ (weight : ℕ → ℝ) (vector : ℕ → Bipartite dA dB),
      (∀ i, 0 ≤ weight i) → HasSum weight 1 →
      (∀ i, ‖vector i‖ = 1) →
      (∀ a b, HasSum
        (fun i => (weight i : ℂ) * QAlgorithms.pureDensity (vector i) a b)
        (normalizedProjector S a b)) →
      (∀ i, 0 < weight i → vector i ∈ S ∧ r ≤ schmidtNumber (vector i)) ∧
      Summable (fun i => weight i * (schmidtNumber (vector i) : ℝ)) ∧
      (r : ℝ) ≤ ∑' i, weight i * (schmidtNumber (vector i) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P43

end
