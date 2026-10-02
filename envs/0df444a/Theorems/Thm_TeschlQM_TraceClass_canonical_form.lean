-- Prove2me | Theorems.Thm_TeschlQM_TraceClass_canonical_form
-- name    : TeschlQM.TraceClass.canonical_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T09:35:50.712243+00:00
-- url     : https://prove2.me/theorems/7e687b10-9877-4a79-8ff8-4e5cec322173
-- title:
--   Theorem 6.7 — Canonical form of compact operators
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space and let $K \in \mathfrak{L}(\mathfrak{H})$ be compact, with adjoint $K^*$. Then there exist orthonormal sets $\{\hat\phi_j\}$ and $\{\phi_j\}$ and positive numbers $s_j = s_j(K) > 0$ such that for every $\psi \in \mathfrak{H}$
--   $$K\psi = \sum_j s_j \langle \phi_j, \psi\rangle \hat\phi_j, \qquad K^*\psi = \sum_j s_j \langle \hat\phi_j, \psi\rangle \phi_j .$$
--   Moreover $K\phi_j = s_j\hat\phi_j$ and $K^*\hat\phi_j = s_j \phi_j$; the numbers $s_j^2$ are exactly the nonzero eigenvalues of $K^*K$, and also of $KK^*$, counted with multiplicity: for every $\mu > 0$ the number of indices $j$ with $s_j^2 = \mu$ equals $\dim\operatorname{Ker}(K^*K - \mu)$ and $\dim\operatorname{Ker}(KK^* - \mu)$. Finally, there are either finitely many $s_j$ or they converge to zero.
--
--   The $s_j(K)$ are the **singular values** of $K$; they are the numbers whose summability defines the Hilbert–Schmidt and trace classes.
--
--   **Formalization Note.** The index set is an arbitrary type in the universe of $\mathfrak{H}$; the series converge unconditionally for each fixed $\psi$ (`HasSum`), i.e. (6.6) holds in the strong sense. Multiplicities are compared in $\{0,1,\dots\}\cup\{\infty\}$ (`ENat.card` and `Cardinal.toENat` of the rank of Mathlib's eigenspace). "Converge to zero" is convergence along the cofinite filter, which is automatic for a finite index set. Compactness is membership in the norm closure of the finite rank operators.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 137, Theorem 6.7

import Mathlib
import Definitions.Def_TeschlQM_Shared_compactOperators

namespace TeschlQM.TraceClass

universe u

open scoped InnerProductSpace
open Filter Topology

/-- Teschl, Theorem 6.7 (canonical form of compact operators), p. 137. Let `K` be compact. There
exist orthonormal sets `{φ̂_j}`, `{φ_j}` and positive numbers `s_j = s_j(K)` such that
`K = ∑_j s_j ⟨φ_j, ·⟩ φ̂_j` and `K* = ∑_j s_j ⟨φ̂_j, ·⟩ φ_j` (6.6), the series converging for every
vector. Moreover `Kφ_j = s_j φ̂_j`, `K*φ̂_j = s_j φ_j`; the numbers `s_j²` are the nonzero eigenvalues
of `KK*`, respectively `K*K`, counted with multiplicity (for each `μ > 0`, the number of `j` with
`s_j² = μ` equals `dim Ker(K*K - μ)` and `dim Ker(KK* - μ)`, as cardinals in `ℕ ∪ {∞}`); and there
are either finitely many `s_j` or they converge to zero (`s_j → 0` along the cofinite filter). -/
theorem canonical_form {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : H →L[ℂ] H) (hK : K ∈ TeschlQM.Shared.compactOperators H) :
    ∃ (ι : Type u) (φhat φ : ι → H) (s : ι → ℝ),
      Orthonormal ℂ φhat ∧ Orthonormal ℂ φ ∧ (∀ j, 0 < s j) ∧
      (∀ ψ : H, HasSum (fun j => ((s j : ℂ) * ⟪φ j, ψ⟫_ℂ) • φhat j) (K ψ)) ∧
      (∀ ψ : H, HasSum (fun j => ((s j : ℂ) * ⟪φhat j, ψ⟫_ℂ) • φ j)
        (ContinuousLinearMap.adjoint K ψ)) ∧
      (∀ j, K (φ j) = (s j : ℂ) • φhat j ∧
        ContinuousLinearMap.adjoint K (φhat j) = (s j : ℂ) • φ j) ∧
      (∀ μ : ℝ, 0 < μ →
        ENat.card {j // s j ^ 2 = μ} = Cardinal.toENat (Module.rank ℂ (Module.End.eigenspace
          ((ContinuousLinearMap.adjoint K ∘L K : H →L[ℂ] H) : H →ₗ[ℂ] H) (μ : ℂ))) ∧
        ENat.card {j // s j ^ 2 = μ} = Cardinal.toENat (Module.rank ℂ (Module.End.eigenspace
          ((K ∘L ContinuousLinearMap.adjoint K : H →L[ℂ] H) : H →ₗ[ℂ] H) (μ : ℂ)))) ∧
      Tendsto s cofinite (𝓝 0) := by sorry

end TeschlQM.TraceClass
