-- Prove2me | Theorems.Thm_TeschlQM_MinMax_min_max
-- name    : TeschlQM.MinMax.min_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:42:13.397978+00:00
-- url     : https://prove2.me/theorems/c2646231-faa8-4de2-8de6-1bbaabefe7ae
-- title:
--   Theorem 4.10 — the min-max principle
-- statement:
--   Let $A$ be a self-adjoint operator on a complex Hilbert space $\mathfrak H$ with domain $\mathfrak D(A)$, and let $E_1 \le E_2 \le E_3 \le \cdots$ be the eigenvalues of $A$ below the essential spectrum, counted according to their multiplicity, respectively the infimum of the essential spectrum once there are no more eigenvalues left. For $\psi_1, \dots, \psi_{n-1} \in \mathfrak H$ let
--   $$U(\psi_1, \dots, \psi_{n-1}) = \{ \psi \in \mathfrak D(A) \mid \|\psi\| = 1,\ \psi \in \operatorname{span}\{\psi_1, \dots, \psi_{n-1}\}^\perp \}.$$
--   Then for every $n \ge 1$
--   $$E_n = \sup_{\psi_1, \dots, \psi_{n-1}} \ \inf_{\psi \in U(\psi_1, \dots, \psi_{n-1})} \langle \psi, A\psi \rangle ,$$
--   where the supremum runs over all $(n-1)$-tuples of vectors of $\mathfrak H$.
--
--   The min-max principle characterizes the eigenvalues below the essential spectrum without knowing the eigenvectors, and is the basis of the Rayleigh–Ritz method for bounding them.
--
--   **Formalization Note.** $E_n$ is `eigenvalueSeq A n`, defined from the spectrum, the essential spectrum $\sigma_{ess}(A) = \sigma(A) \setminus \sigma_d(A)$ of p. 145 and the dimensions of eigenspaces (cardinals), not from the min-max expression. All values are in `EReal`: the infimum over an empty $U$ is $+\infty$ and the equality also covers the cases the book leaves implicit ($A$ unbounded below, where both sides are $-\infty$; $\sigma_{ess}(A) = \emptyset$ with fewer than $n$ eigenvalues, where both sides are $+\infty$). $\langle\psi, A\psi\rangle$ enters through its real part. For $n = 1$ the tuple is empty and $U$ is the unit sphere of $\mathfrak D(A)$. No projection-valued measure is used, and the Hilbert space is not assumed separable.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 119, Theorem 4.10

import Mathlib
import Definitions.Def_TeschlQM_MinMax_eigenvalueSeq
import Definitions.Def_TeschlQM_MinMax_minMaxSet

open scoped InnerProductSpace

namespace TeschlQM.MinMax

/-- Teschl, Theorem 4.10 (Min-max), p. 119, (4.32): let `A` be self-adjoint and let
`E₁ ≤ E₂ ≤ E₃ ≤ ⋯` be the eigenvalues of `A` below the essential spectrum (counted with
multiplicity), respectively `inf σ_ess(A)` once there are no more eigenvalues left
(`eigenvalueSeq A n`). Then for every `n ≥ 1`
`E_n = sup_{ψ₁, …, ψ_{n−1} ∈ ℌ} inf_{ψ ∈ U(ψ₁, …, ψ_{n−1})} ⟨ψ, Aψ⟩`, with `U` as in (4.28).
Values are in `EReal`; an infimum over an empty `U` is `+∞`. -/
theorem min_max {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (n : ℕ) (hn : 1 ≤ n) :
    eigenvalueSeq A n =
      ⨆ ψ : Fin (n - 1) → H, ⨅ φ ∈ minMaxSet A ψ, ((⟪(φ : H), A φ⟫_ℂ).re : EReal) := by sorry

end TeschlQM.MinMax
