-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_compressionOuter
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.compressionOuter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:17:31.330432+00:00
-- url     : https://prove2.me/theorems/e9c9a5b4-ac97-47ad-b81c-d89f974b0850
-- title:
--   Distributed compression outer bound
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\phi^{RAB}$ be a fixed pure source. Write $SW(\phi)$ for the Euclidean closure of nonnegative rate pairs obtainable by independent CPTP encoders on $A^n$ and $B^n$, followed by Charlie's CPTP decoder. A rate is obtainable if every error $\epsilon>0$ is attained for every sufficiently large $n$, with message dimensions at most $2^{nQ_A}$ and $2^{nQ_B}$, and overlap with the complete pure target at least $1-\epsilon$. No communication between senders, classical communication, or shared assistance is supplied. Put $J(A;B)=H(A)+H(B)+H(AB)$.
--
--   Define $E_{\rm sq}(\phi^{AB})$ as the infimum of $\tfrac12 I(A;B|E)$ over all density-matrix extensions, allowing every finite nonempty extension dimension. Every $(Q_A,Q_B)\in SW(\phi)$ satisfies
--
--   $$
--   Q_A\ge\tfrac12 I(A;R)_\phi,\qquad Q_B\ge\tfrac12 I(B;R)_\phi,\qquad Q_A+Q_B\ge\tfrac12 J(A;B)_\phi-E_{\rm sq}(\phi^{AB}).
--   $$
--
--   Squashed entanglement is subtracted once from the sum constraint. This bounds every CPTP compression code, rather than only codes obtained from FQSW.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 18, Theorem X.2, Eq. (51)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem X.2, PDF p.18, Eq.(51): outer bound for every CPTP compression code.
Squashed-entanglement additivity is cited background [26], not an extra hypothesis. -/
theorem compressionOuter {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi) :
    compressionRegion (pureDensity phi) ⊆
      rateRegion (pureDensity phi) (squashed (traceLeft (pureDensity phi))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
