-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_depolarizingIndependentEventRange
-- name    : QAlgorithms.Papers.Independent.Information100.P39.depolarizingIndependentEventRange
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:22:50.055438+00:00
-- url     : https://prove2.me/theorems/06d0e602-223b-4324-997c-678af0c243de
-- title:
--   Appendix A.1: exact depolarizing independent-event range
-- statement:
--   For $p\in[0,1]$, let $\nu_p=(1-p,p/3,p/3,p/3)$ be depolarizing noise, with $p$ the total nonidentity probability. Then
--
--   $$\nu_p\text{ has an independent-event representation}\quad\Longleftrightarrow\quad p\le\tfrac34.$$
--
--   For $p\le3/4$, the law is realized by independent $X,Y,Z$ events with common probability
--
--   $$r(p)=\frac{1-\sqrt{1-4p/3}}2\in[0,1/2].$$
--
--   For $p>3/4$, the product of its three nontrivial Fourier coefficients is negative. This pins the exact inclusion range, including the noiseless and completely depolarized endpoints.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 8, Appendix A.1: exact depolarizing independent-event range

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Appendix A.1, PDF pp.8–9: the exact range and the equal-event construction. -/
theorem depolarizingIndependentEventRange (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Learning.IsDistribution (depolarizingLaw p) ∧
    (HasIndependentEvents (depolarizingLaw p) ↔ p ≤ 3/4) ∧
    (p ≤ 3/4 → depolarizingEventProbability p ∈ Set.Icc 0 (1/2) ∧
      depolarizingLaw p = eventLaw xyzEvents (fun _ => depolarizingEventProbability p)) ∧
    (3/4 < p →
      SparsePauliNoise.eigenvalueWHT (depolarizingLaw p) labelX *
      SparsePauliNoise.eigenvalueWHT (depolarizingLaw p) labelY *
      SparsePauliNoise.eigenvalueWHT (depolarizingLaw p) labelZ < 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
