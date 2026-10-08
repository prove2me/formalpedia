-- Prove2me | Theorems.Thm_TeschlQM_MinMax_eigenvalueSeq_mono
-- name    : TeschlQM.MinMax.eigenvalueSeq_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:45:53.329867+00:00
-- url     : https://prove2.me/theorems/c88d08aa-b944-456e-9a88-7cb3a583400d
-- title:
--   Corollary 4.11 — A ≥ B implies Eₙ(A) ≥ Eₙ(B)
-- statement:
--   Let $A$ and $B$ be self-adjoint operators on a complex Hilbert space $\mathfrak H$ with $A \ge B$, i.e. $A - B \ge 0$, where $\mathfrak D(A) \subseteq \mathfrak D(B)$ and
--   $$\langle \psi, (A - B)\psi \rangle \ge 0 \qquad \text{for all } \psi \in \mathfrak D(A - B) = \mathfrak D(A).$$
--   Then for every $n \ge 1$,
--   $$E_n(A) \ge E_n(B),$$
--   where $E_n(\cdot)$ are the eigenvalues below the essential spectrum counted with multiplicity, respectively the infimum of the essential spectrum, as in the min-max principle.
--
--   Increasing an operator can only raise each of these eigenvalues.
--
--   **Formalization Note.** The book writes only "$A - B \ge 0$". Read literally on $\mathfrak D(A) \cap \mathfrak D(B)$ the statement would be false (that intersection can be $\{0\}$), so the operator $A - B$ is taken with domain $\mathfrak D(A)$, i.e. the hypothesis $\mathfrak D(A) \subseteq \mathfrak D(B)$ is stated, which is the reading under which the corollary follows from (4.32). $E_n$ is `eigenvalueSeq` (values in `EReal`).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 119, Corollary 4.11

import Mathlib
import Definitions.Def_TeschlQM_MinMax_eigenvalueSeq

open scoped InnerProductSpace

namespace TeschlQM.MinMax

/-- Teschl, Corollary 4.11, p. 119: if `A` and `B` are self-adjoint with `A ≥ B`, i.e.
`A − B ≥ 0`, then `E_n(A) ≥ E_n(B)` for every `n ≥ 1`. Here `A − B ≥ 0` is read with
`𝔇(A − B) = 𝔇(A) ∩ 𝔇(B) = 𝔇(A)`: `𝔇(A) ⊆ 𝔇(B)` and `⟨ψ, (A − B)ψ⟩ ≥ 0` for `ψ ∈ 𝔇(A)`. -/
theorem eigenvalueSeq_mono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hdom : A.domain ≤ B.domain)
    (hAB : ∀ (ψ : H) (hψA : ψ ∈ A.domain) (hψB : ψ ∈ B.domain),
      0 ≤ (⟪ψ, A ⟨ψ, hψA⟩ - B ⟨ψ, hψB⟩⟫_ℂ).re)
    (n : ℕ) (hn : 1 ≤ n) :
    eigenvalueSeq B n ≤ eigenvalueSeq A n := by sorry

end TeschlQM.MinMax
