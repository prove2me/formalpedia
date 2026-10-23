-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_singleQubitFourierCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P39.singleQubitFourierCriterion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:21:09.842976+00:00
-- url     : https://prove2.me/theorems/ebbce0d7-85ec-4829-a33c-c9eee2e6aea3
-- title:
--   Appendix A.1: exact single-qubit independent-event criterion
-- statement:
--   Let $\nu$ be a probability law on single-qubit Paulis modulo phase, and define its unnormalized symplectic Walsh transform by $\widehat\nu(u)=\sum_E\nu(E)(-1)^{[u,E]}$. The law has a representation by finitely many independent Bernoulli Pauli events if and only if there are $\alpha,\beta,\gamma\in[-1,1]$ such that
--
--   $$(\widehat\nu(X),\widehat\nu(Y),\widehat\nu(Z))=(\beta\gamma,\alpha\gamma,\alpha\beta).$$
--
--   Every such factorization is realized by independent $X,Y,Z$ events with probabilities $(1-\alpha)/2,(1-\beta)/2,(1-\gamma)/2$. Consequently the product of the three Fourier coefficients is nonnegative. Every independent-event law is a deterministic Pauli translate of an independent-event law with all event probabilities at most $1/2$ and nonnegative Fourier coefficients. This characterizes the class while retaining the qualification needed for arbitrary event probabilities.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 8, Appendix A.1: exact single-qubit independent-event criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Appendix A.1, PDF p.8, Eqs.(S2)–(S4): characterization, explicit converse,
sign obstruction, and deterministic-translate qualification. Positivity alone
is not the characterization. -/
theorem singleQubitFourierCriterion (nu : PauliLabel 1 → ℝ)
    (hnu : Learning.IsDistribution nu) :
    (HasIndependentEvents nu ↔ ∃ a b c : ℝ,
      a ∈ Set.Icc (-1) 1 ∧ b ∈ Set.Icc (-1) 1 ∧ c ∈ Set.Icc (-1) 1 ∧
      FourierFactors nu a b c) ∧
    (∀ a b c : ℝ, a ∈ Set.Icc (-1) 1 → b ∈ Set.Icc (-1) 1 →
      c ∈ Set.Icc (-1) 1 → FourierFactors nu a b c →
      nu = eventLaw xyzEvents (![(1-a)/2, (1-b)/2, (1-c)/2])) ∧
    (HasIndependentEvents nu →
      0 ≤ SparsePauliNoise.eigenvalueWHT nu labelX *
        SparsePauliNoise.eigenvalueWHT nu labelY *
        SparsePauliNoise.eigenvalueWHT nu labelZ ∧
      ∃ t : PauliLabel 1, ∃ mu : PauliLabel 1 → ℝ,
        Learning.IsDistribution mu ∧ HasSmallEvents mu ∧
        (∀ u, 0 ≤ SparsePauliNoise.eigenvalueWHT mu u) ∧
        nu = fun u => mu (u - t)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
