-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_compressionInner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.compressionInner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:16:53.138464+00:00
-- url     : https://prove2.me/theorems/3a457280-5a6a-4a80-ab0c-6d3cd69b5cf2
-- title:
--   Distributed compression inner bound
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\phi^{RAB}$ be a fixed pure source. Write $SW(\phi)$ for the Euclidean closure of nonnegative rate pairs obtainable by independent CPTP encoders on $A^n$ and $B^n$, followed by Charlie's CPTP decoder. A rate is obtainable if every error $\epsilon>0$ is attained for every sufficiently large $n$, with message dimensions at most $2^{nQ_A}$ and $2^{nQ_B}$, and overlap with the complete pure target at least $1-\epsilon$. No communication between senders, classical communication, or shared assistance is supplied. Put $J(A;B)=H(A)+H(B)+H(AB)$.
--
--   Every nonnegative pair satisfying
--
--   $$
--   Q_A\ge\tfrac12 I(A;R)_\phi,\qquad Q_B\ge\tfrac12 I(B;R)_\phi,\qquad Q_A+Q_B\ge\tfrac12 J(A;B)_\phi
--   $$
--
--   belongs to $SW(\phi)$. All three boundaries are included.
--
--   This is the FQSW-based inner bound after time sharing and closure.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 15, Theorem X.1, Eq. (38)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem X.1, PDF p.15, Eq.(38): inner bound, including all boundary points. -/
theorem compressionInner {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi) :
    rateRegion (pureDensity phi) 0 ⊆ compressionRegion (pureDensity phi) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
