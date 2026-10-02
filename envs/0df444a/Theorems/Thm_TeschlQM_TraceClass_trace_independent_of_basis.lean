-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_trace_independent_of_basis
-- name    : TeschlQM.TraceClass.trace_independent_of_basis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:59:24.538879+00:00
-- url     : https://prove2.me/theorems/f9104bb7-c372-4e7e-937b-0a2bef6ce20d
-- title:
--   Lemma 6.15 — The trace of a trace class operator is finite and basis independent
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and let $K$ be a trace class operator on $\mathfrak{H}$. Then for every orthonormal basis $\{\varphi_n\}$ of $\mathfrak{H}$ the series
--   $$\operatorname{tr}(K) = \sum_n \langle \varphi_n, K\varphi_n\rangle$$
--   converges, and its value is the same for every orthonormal basis. In particular it equals the trace $\operatorname{tr}(K)$ computed in the fixed basis of the definition.
--
--   This is what makes the trace a well-defined linear functional on the trace class, and it explains the name "trace class".
--
--   **Formalization Note.** "Converges" is Mathlib's `Summable` over the index set of the basis, i.e. unconditional convergence, which in $\mathbb{C}$ is absolute convergence. This is essential: Mathlib's `tsum` of a non-summable family is $0$, so independence of the basis alone would say nothing about divergent series. Orthonormal bases are Mathlib's `HilbertBasis` with arbitrary index types in arbitrary universes; no separability is assumed (the book's $\mathfrak{H}$ is separable, and the statement for all Hilbert spaces contains the book's).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 143, Lemma 6.15

import Mathlib
import Definitions.Def_TeschlQM_TraceClass_schattenClass
import Definitions.Def_TeschlQM_TraceClass_trace

namespace TeschlQM.TraceClass

universe v w

open scoped InnerProductSpace

/-- Teschl, Lemma 6.15, p. 143. If `K` is trace class, then for any orthonormal basis `{φ_n}` the
trace `tr(K) = ∑_n ⟨φ_n, Kφ_n⟩` (6.26) is finite and independent of the orthonormal basis: for every
Hilbert basis the family `⟨φ_n, Kφ_n⟩` is summable (unconditionally, hence absolutely, in `ℂ`), any
two Hilbert bases give the same sum, and that sum is `trace K`. -/
theorem trace_independent_of_basis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : H →L[ℂ] H) (hK : IsTraceClass K) :
    (∀ (ι : Type v) (φ : HilbertBasis ι ℂ H), Summable (fun n => ⟪φ n, K (φ n)⟫_ℂ)) ∧
    (∀ (ι : Type v) (κ : Type w) (φ : HilbertBasis ι ℂ H) (ψ : HilbertBasis κ ℂ H),
      ∑' n, ⟪φ n, K (φ n)⟫_ℂ = ∑' m, ⟪ψ m, K (ψ m)⟫_ℂ) ∧
    (∀ (ι : Type v) (φ : HilbertBasis ι ℂ H), ∑' n, ⟪φ n, K (φ n)⟫_ℂ = trace K) := by sorry

end TeschlQM.TraceClass
