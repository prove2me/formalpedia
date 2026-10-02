-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_traceClass_iff_mul_hilbertSchmidt
-- name    : TeschlQM.TraceClass.traceClass_iff_mul_hilbertSchmidt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:53:46.64057+00:00
-- url     : https://prove2.me/theorems/2cffabcf-a057-4845-93ef-a87e6cfca69c
-- title:
--   Lemma 6.13 — Trace class = products of two Hilbert–Schmidt operators
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and $K \in \mathfrak{L}(\mathfrak{H})$. Then $K$ is trace class if and only if it can be written as a product $K = K_1K_2$ of two Hilbert–Schmidt operators $K_1, K_2$; and in this case, for every such factorization,
--   $$\|K\|_1 \le \|K_1\|_2\,\|K_2\|_2 .$$
--
--   Since Hilbert–Schmidt operators are easy to recognize (Lemma 6.10), this is the standard way to show that an operator is trace class, and it is the key step in the proof that the trace is well defined.
--
--   **Formalization Note.** Products are compositions in `H →L[ℂ] H`; the norms are compared in $[0,\infty]$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 142–143, Lemma 6.13

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass

namespace TeschlQM.TraceClass

/-- Teschl, Lemma 6.13, pp. 142–143. An operator is trace class if and only if it can be written as
the product of two Hilbert–Schmidt operators, `K = K₁K₂`, and in this case (for every such
factorization) `‖K‖₁ ≤ ‖K₁‖₂‖K₂‖₂` (6.24). -/
theorem traceClass_iff_mul_hilbertSchmidt {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : H →L[ℂ] H) :
    (IsTraceClass K ↔
      ∃ K₁ K₂ : H →L[ℂ] H, IsHilbertSchmidt K₁ ∧ IsHilbertSchmidt K₂ ∧ K = K₁ * K₂) ∧
    (∀ K₁ K₂ : H →L[ℂ] H, IsHilbertSchmidt K₁ → IsHilbertSchmidt K₂ → K = K₁ * K₂ →
      schattenNorm 1 K ≤ schattenNorm 2 K₁ * schattenNorm 2 K₂) := by sorry

end TeschlQM.TraceClass
