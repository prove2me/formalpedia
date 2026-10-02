-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_hilbertSchmidt_star_ideal
-- name    : TeschlQM.TraceClass.hilbertSchmidt_star_ideal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:47:14.44498+00:00
-- url     : https://prove2.me/theorems/dd86cd39-40c7-4f88-a8cc-768fc9aaafa3
-- title:
--   Corollary 6.11 — Hilbert–Schmidt operators form a ∗-ideal
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space. The set of Hilbert–Schmidt operators is a $*$-ideal in $\mathfrak{L}(\mathfrak{H})$: it contains $0$, is closed under sums, scalar multiples and adjoints, and for every Hilbert–Schmidt $K$ and every bounded $A$ the products $KA$ and $AK$ are Hilbert–Schmidt, with
--   $$\|KA\|_2 \le \|A\|\,\|K\|_2, \qquad \|AK\|_2 \le \|A\|\,\|K\|_2 .$$
--
--   Here $\|A\|$ is the operator norm and $\|\cdot\|_2$ the Hilbert–Schmidt norm.
--
--   **Formalization Note.** Products are compositions in `H →L[ℂ] H`; the adjoint is Mathlib's `ContinuousLinearMap.adjoint`. Norm inequalities are stated in $[0,\infty]$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 141, Corollary 6.11

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass

namespace TeschlQM.TraceClass

open scoped ENNReal

/-- Teschl, Corollary 6.11, p. 141. The set of Hilbert–Schmidt operators forms a `∗`-ideal in
`𝔏(ℌ)`: it contains `0`, is closed under sums and scalar multiples, under multiplication by an
arbitrary bounded operator `A` on either side, and under taking adjoints; and
`‖KA‖₂ ≤ ‖A‖‖K‖₂`, respectively `‖AK‖₂ ≤ ‖A‖‖K‖₂` (6.18). -/
theorem hilbertSchmidt_star_ideal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    IsHilbertSchmidt (0 : H →L[ℂ] H) ∧
    (∀ K L : H →L[ℂ] H, IsHilbertSchmidt K → IsHilbertSchmidt L → IsHilbertSchmidt (K + L)) ∧
    (∀ (c : ℂ) (K : H →L[ℂ] H), IsHilbertSchmidt K → IsHilbertSchmidt (c • K)) ∧
    (∀ K : H →L[ℂ] H, IsHilbertSchmidt K → IsHilbertSchmidt (ContinuousLinearMap.adjoint K)) ∧
    (∀ K A : H →L[ℂ] H, IsHilbertSchmidt K →
      IsHilbertSchmidt (K * A) ∧ IsHilbertSchmidt (A * K) ∧
      schattenNorm 2 (K * A) ≤ (‖A‖₊ : ℝ≥0∞) * schattenNorm 2 K ∧
      schattenNorm 2 (A * K) ≤ (‖A‖₊ : ℝ≥0∞) * schattenNorm 2 K) := by sorry

end TeschlQM.TraceClass
