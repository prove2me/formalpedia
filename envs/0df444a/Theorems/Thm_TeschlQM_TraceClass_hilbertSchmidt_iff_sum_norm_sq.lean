-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_hilbertSchmidt_iff_sum_norm_sq
-- name    : TeschlQM.TraceClass.hilbertSchmidt_iff_sum_norm_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:41:59.139713+00:00
-- url     : https://prove2.me/theorems/433a2551-762a-4dec-8d03-58fe2ee7285e
-- title:
--   Lemma 6.10 — Hilbert–Schmidt operators via an orthonormal basis
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and let $K \in \mathfrak{L}(\mathfrak{H})$ be compact. Then $K$ is Hilbert–Schmidt, i.e. $\sum_j s_j(K)^2 < \infty$, if and only if
--   $$\sum_n \|K\psi_n\|^2 < \infty$$
--   for some orthonormal basis $\{\psi_n\}$ of $\mathfrak{H}$; and in this case
--   $$\sum_n \|K\psi_n\|^2 = \|K\|_2^2$$
--   for any orthonormal basis $\{\psi_n\}$.
--
--   This is the practical test for the Hilbert–Schmidt property and the tool behind Corollary 6.11 and Lemma 6.13.
--
--   **Formalization Note.** Orthonormal bases are Mathlib's `HilbertBasis`, with arbitrary index types (no separability is assumed; the existential basis is indexed in the universe of $\mathfrak{H}$). The sums of the nonnegative terms $\|K\psi_n\|^2$ and the norm $\|K\|_2$ are taken in $[0,\infty]$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 140, Lemma 6.10

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass

namespace TeschlQM.TraceClass

universe u v

open scoped ENNReal

/-- Teschl, Lemma 6.10, p. 140. A compact operator `K` is Hilbert–Schmidt if and only if
`∑_n ‖Kψ_n‖² < ∞` (6.16) for some orthonormal basis `{ψ_n}`, and in this case
`∑_n ‖Kψ_n‖² = ‖K‖₂²` (6.17) for any orthonormal basis. Sums of the nonnegative terms `‖Kψ_n‖²` are
taken in `[0, ∞]`. -/
theorem hilbertSchmidt_iff_sum_norm_sq {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (K : H →L[ℂ] H) (hK : K ∈ TeschlQM.Shared.compactOperators H) :
    (IsHilbertSchmidt K ↔
      ∃ (ι : Type u) (ψ : HilbertBasis ι ℂ H), ∑' n, (‖K (ψ n)‖₊ : ℝ≥0∞) ^ 2 < ⊤) ∧
    (IsHilbertSchmidt K → ∀ (ι : Type v) (ψ : HilbertBasis ι ℂ H),
      ∑' n, (‖K (ψ n)‖₊ : ℝ≥0∞) ^ 2 = schattenNorm 2 K ^ 2) := by sorry

end TeschlQM.TraceClass
