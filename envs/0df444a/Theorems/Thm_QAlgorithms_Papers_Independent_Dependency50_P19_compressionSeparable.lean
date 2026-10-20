-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_compressionSeparable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.compressionSeparable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:18:16.071717+00:00
-- url     : https://prove2.me/theorems/047422d5-f5f4-40b4-890e-55ac6b69eee1
-- title:
--   Exact distributed region for every separable source
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\phi^{RAB}$ be a fixed pure source. Write $SW(\phi)$ for the Euclidean closure of nonnegative rate pairs obtainable by independent CPTP encoders on $A^n$ and $B^n$, followed by Charlie's CPTP decoder. A rate is obtainable if every error $\epsilon>0$ is attained for every sufficiently large $n$, with message dimensions at most $2^{nQ_A}$ and $2^{nQ_B}$, and overlap with the complete pure target at least $1-\epsilon$. No communication between senders, classical communication, or shared assistance is supplied. Put $J(A;B)=H(A)+H(B)+H(AB)$.
--
--   If $\phi^{AB}$ is a convex combination of product density matrices, then
--
--   $$
--   SW(\phi)=\{(Q_A,Q_B)\in\mathbb R_{\ge0}^2:\;Q_A\ge\tfrac12 I(A;R)_\phi,\qquad Q_B\ge\tfrac12 I(B;R)_\phi,\qquad Q_A+Q_B\ge\tfrac12 J(A;B)_\phi\}.
--   $$
--
--   No irreducibility condition is required. This identifies the exact region for all separable sources, including product sources.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 18, Section X, following Eq. (51)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section X, PDF p.18: exact region for every separable source; no irreducibility
hypothesis from the cited earlier result [27] is imposed. -/
theorem compressionSeparable {R A B : Type*} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq R] [DecidableEq A] [DecidableEq B]
    [Nonempty R] [Nonempty A] [Nonempty B]
    (phi : EuclideanSpace ℂ (R × (A × B))) (hphi : IsState phi)
    (hsep : Entanglement.IsSeparableDensity (traceLeft (pureDensity phi))) :
    compressionRegion (pureDensity phi) = rateRegion (pureDensity phi) 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
