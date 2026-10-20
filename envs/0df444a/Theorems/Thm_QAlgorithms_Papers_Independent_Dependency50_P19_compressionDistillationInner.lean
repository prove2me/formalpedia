-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_compressionDistillationInner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.compressionDistillationInner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:19:02.444974+00:00
-- url     : https://prove2.me/theorems/22bfcc83-85e9-4317-a56e-9c311b965307
-- title:
--   No-communication-distillation compression improvement
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\phi^{RAB}$ be a fixed pure source. Write $SW(\phi)$ for the Euclidean closure of nonnegative rate pairs obtainable by independent CPTP encoders on $A^n$ and $B^n$, followed by Charlie's CPTP decoder. A rate is obtainable if every error $\epsilon>0$ is attained for every sufficiently large $n$, with message dimensions at most $2^{nQ_A}$ and $2^{nQ_B}$, and overlap with the complete pure target at least $1-\epsilon$. No communication between senders, classical communication, or shared assistance is supplied. Put $J(A;B)=H(A)+H(B)+H(AB)$.
--
--   Let $D_0(\phi^{AB})$ be the supremum of nonnegative rates of EPR distillation by separate local CPTP maps, with no messages or assistance: for every positive error and rate slack, every sufficiently large block yields a normalized EPR state within that error and with logarithmic local dimension at least $n(D-\delta)$. Then every nonnegative pair satisfying
--
--   $$
--   Q_A\ge\tfrac12 I(A;R)_\phi,\qquad Q_B\ge\tfrac12 I(B;R)_\phi,\qquad Q_A+Q_B\ge\tfrac12 J(A;B)_\phi-D_0(\phi^{AB})
--   $$
--
--   belongs to $SW(\phi)$. Both individual constraints are unchanged.
--
--   This strengthens the FQSW inner sum bound using operational local-only distillation, not LOCC distillation.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 18, Section X, Eq. (52)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section X, PDF p.18, Eq.(52): local-only distillation improves the sum
constraint, leaving both individual constraints unchanged. -/
theorem compressionDistillationInner {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi) :
    rateRegion (pureDensity phi) (localDistillable (traceLeft (pureDensity phi))) ⊆
      compressionRegion (pureDensity phi) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
