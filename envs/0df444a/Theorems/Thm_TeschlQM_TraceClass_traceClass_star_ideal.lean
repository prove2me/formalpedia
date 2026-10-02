-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_traceClass_star_ideal
-- name    : TeschlQM.TraceClass.traceClass_star_ideal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:56:39.445499+00:00
-- url     : https://prove2.me/theorems/144195e2-1150-4566-b753-e5bcd403c744
-- title:
--   Corollary 6.14 — Trace class operators form a ∗-ideal
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space. The set of trace class operators is a $*$-ideal in $\mathfrak{L}(\mathfrak{H})$: it contains $0$, is closed under sums, scalar multiples and adjoints, and for every trace class $K$ and every bounded $A$ the products $KA$ and $AK$ are trace class, with
--   $$\|KA\|_1 \le \|A\|\,\|K\|_1, \qquad \|AK\|_1 \le \|A\|\,\|K\|_1 .$$
--
--   **Formalization Note.** Products are compositions in `H →L[ℂ] H`; the adjoint is Mathlib's `ContinuousLinearMap.adjoint`. Norm inequalities are stated in $[0,\infty]$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 143, Corollary 6.14

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass

namespace TeschlQM.TraceClass

open scoped ENNReal

/-- Teschl, Corollary 6.14, p. 143. The set of trace class operators forms a `∗`-ideal in `𝔏(ℌ)`:
it contains `0`, is closed under sums and scalar multiples, under multiplication by an arbitrary
bounded operator `A` on either side, and under taking adjoints; and
`‖KA‖₁ ≤ ‖A‖‖K‖₁`, respectively `‖AK‖₁ ≤ ‖A‖‖K‖₁` (6.25). -/
theorem traceClass_star_ideal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    IsTraceClass (0 : H →L[ℂ] H) ∧
    (∀ K L : H →L[ℂ] H, IsTraceClass K → IsTraceClass L → IsTraceClass (K + L)) ∧
    (∀ (c : ℂ) (K : H →L[ℂ] H), IsTraceClass K → IsTraceClass (c • K)) ∧
    (∀ K : H →L[ℂ] H, IsTraceClass K → IsTraceClass (ContinuousLinearMap.adjoint K)) ∧
    (∀ K A : H →L[ℂ] H, IsTraceClass K →
      IsTraceClass (K * A) ∧ IsTraceClass (A * K) ∧
      schattenNorm 1 (K * A) ≤ (‖A‖₊ : ℝ≥0∞) * schattenNorm 1 K ∧
      schattenNorm 1 (A * K) ≤ (‖A‖₊ : ℝ≥0∞) * schattenNorm 1 K) := by sorry

end TeschlQM.TraceClass
