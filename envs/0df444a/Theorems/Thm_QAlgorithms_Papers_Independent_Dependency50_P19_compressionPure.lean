-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_compressionPure
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.compressionPure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:20:24.353076+00:00
-- url     : https://prove2.me/theorems/7bcd13d7-0509-45b2-b050-b8cffadc142b
-- title:
--   Zero communication for a fixed pure bipartite source
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\phi^{RAB}$ be a fixed pure source. Write $SW(\phi)$ for the Euclidean closure of nonnegative rate pairs obtainable by independent CPTP encoders on $A^n$ and $B^n$, followed by Charlie's CPTP decoder. A rate is obtainable if every error $\epsilon>0$ is attained for every sufficiently large $n$, with message dimensions at most $2^{nQ_A}$ and $2^{nQ_B}$, and overlap with the complete pure target at least $1-\epsilon$. No communication between senders, classical communication, or shared assistance is supplied. Put $J(A;B)=H(A)+H(B)+H(AB)$.
--
--   If the marginal $\phi^{AB}$ is itself pure, then
--
--   $$SW(\phi)=\mathbb R_{\ge0}^2.$$
--
--   The reference is then uncorrelated with $AB$, and Charlie can prepare the fixed source locally. This is an exact source-specific compression region, not a statement about an unknown ensemble of pure states.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 20, Section XII, exact pure-source case

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section XII, PDF p.20: for a fixed pure AB marginal, Charlie can prepare it;
SW is the whole nonnegative quadrant. This is not an unknown-ensemble claim. -/
theorem compressionPure {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi)
    (hpure : ∃ v : EuclideanSpace ℂ (A × B), IsState v ∧
      traceLeft (pureDensity phi) = pureDensity v) :
    compressionRegion (pureDensity phi) = {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
