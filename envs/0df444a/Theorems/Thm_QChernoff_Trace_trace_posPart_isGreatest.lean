-- Prove2me | Theorems.Thm_QChernoff_Trace_trace_posPart_isGreatest
-- name    : QChernoff.Trace.trace_posPart_isGreatest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:36.136071+00:00
-- url     : https://prove2.me/theorems/71392694-6397-4a3f-a434-d66bcfb87210
-- title:
--   Proof of Theorem 1, p. 3 — $\operatorname{Tr}[H_+]$ is the maximum of $\operatorname{Tr}[QH]$ over self-adjoint projectors $Q$
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space and $K$ a self-adjoint trace-class operator on $\mathcal H$, with positive part $K_+=(|K|+K)/2$. Then
--
--   $$\operatorname{Tr}[K_+]=\max\big\{\operatorname{Tr}[QK]\ :\ Q=Q^*=Q^2\big\},$$
--
--   that is, $\operatorname{Tr}[QK]\le\operatorname{Tr}[K_+]$ for every orthogonal projection $Q$, and the value $\operatorname{Tr}[K_+]$ is attained by some orthogonal projection.
--
--   (The paper calls the operator $H$; here $K$ is used because $H$ names the Hilbert space.) In the proof of Theorem 1 this bounds $\operatorname{Tr}[P(a-b)]$ by $\operatorname{Tr}[(a-b)_+]$.
--
--   **Formalization Note** $H$ is a complex Hilbert space of arbitrary dimension; operators are continuous linear maps $H\to H$ and $A\ge 0$ is the Loewner order of Mathlib. Trace class and the trace are the platform definitions `IsModulusTraceClass` (summability of $\langle e_i,|T|e_i\rangle$ over a fixed Hilbert basis) and `basisOperatorTrace` ($\sum_i\langle e_i,Te_i\rangle$) of `QAlgorithms_Papers_Independent_Next46_P02`, with scalar field $\mathbb C$. Inequalities between traces are in the partial order of $\mathbb C$, so they also assert that the two sides have the same imaginary part (both are real).
--
--   Differences from the source:
--   - generalization: positive operators of unspecified dimension (matrices in the paper's computations) → bounded operators on an arbitrary complex Hilbert space H, with no finite-dimensionality or separability assumption; reason: p. 3 states that the proof goes through in infinite dimensions; the case H = ℂⁿ is the matrix statement, so every instance of the source is an instance of the Lean statement
--   - encoding: Tr of the products formed from the positive operators K → K trace class (IsModulusTraceClass) and Tr the basis sum basisOperatorTrace; reason: the hypotheses exclude only operators whose traces in the statement are undefined; in finite dimension every operator is trace class, so no instance of the matrix statement is lost
--   - encoding: "Tr[H₊] is the maximum of Tr[QH] over all self-adjoint projectors Q" → IsGreatest {Tr[QK] : Q a star projection} Tr[K⁺] in the partial order of ℂ; reason: IsGreatest is exactly 'upper bound and attained'; IsStarProjection Q (Q* = Q, Q² = Q) is a self-adjoint projector; the order of ℂ compares the real values and asserts each Tr[QK] is real
-- source:
--   Audenaert et al., The Quantum Chernoff Bound, arXiv:quant-ph/0610027v1, p. 3, proof of Theorem 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02
import Definitions.Def_QChernoff_Trace_Power
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Next46.P02

namespace QChernoff.Trace

/-- Proof of Theorem 1, p. 3: for self-adjoint trace-class `K`, `Tr[K₊]` is the maximum of
`Tr[QK]` over all self-adjoint (orthogonal) projections `Q`. -/
theorem trace_posPart_isGreatest {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : H →L[ℂ] H) (hK : IsSelfAdjoint K) (hKtr : IsModulusTraceClass K) :
    IsGreatest {z : ℂ | ∃ Q : H →L[ℂ] H, IsStarProjection Q ∧ z = basisOperatorTrace (Q * K)}
      (basisOperatorTrace K⁺) := by sorry

end QChernoff.Trace
