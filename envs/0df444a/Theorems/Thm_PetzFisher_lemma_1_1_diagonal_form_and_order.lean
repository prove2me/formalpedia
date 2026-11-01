-- Prove2me | Theorems.Thm_PetzFisher_lemma_1_1_diagonal_form_and_order
-- name    : PetzFisher.lemma_1_1_diagonal_form_and_order
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:09.290412+00:00
-- url     : https://prove2.me/theorems/ba71074b-b232-44b6-848a-d68a4327dfdd
-- title:
--   Lemma 1.1 — Hadamard form of $\mathbb J^f_D$ for diagonal $D$, and $0\le\mathbb J^{f_1}_D\le\mathbb J^{f_2}_D$ for $f_1\le f_2$
-- statement:
--   Let $f:\mathbb R^+\to\mathbb R^+$ be continuous.
--
--   1. If $D=\mathrm{Diag}(\lambda_1,\dots,\lambda_n)$ with all $\lambda_i>0$, then for every $B\in M_n$
--   $$
--   (\mathbb J^f_D B)_{ij}=\lambda_j\,f\!\left(\frac{\lambda_i}{\lambda_j}\right)B_{ij}.
--   $$
--   2. If $f_1,f_2:\mathbb R^+\to\mathbb R^+$ are continuous with $f_1\le f_2$, then
--   $$
--   0\le\mathbb J^{f_1}_D\le\mathbb J^{f_2}_D
--   $$
--   as operators on $M_n$ with the Hilbert–Schmidt inner product $\langle X,Y\rangle=\operatorname{Tr}X^*Y$: for every complex matrix $B$, $\langle B,\mathbb J^{f_1}_DB\rangle$ and $\langle B,\mathbb J^{f_2}_DB\rangle$ are real and $0\le\langle B,\mathbb J^{f_1}_DB\rangle\le\langle B,\mathbb J^{f_2}_DB\rangle$. This is stated for every positive definite $D$.
--
--   The lemma makes $\mathbb J^f_D$ a Hadamard (Schur) multiplier in the eigenbasis of $D$ and shows that the order of functions is the order of the corresponding operators; in particular the arithmetic mean gives the largest and the harmonic mean the smallest $\mathbb J^f_D$ among standard functions.
--
--   **Formalization Note** $f:\mathbb R^+\to\mathbb R^+$ is a real function that is continuous and nonnegative on $(0,\infty)$, and $f_1\le f_2$ is pointwise on $(0,\infty)$. The operator inequalities are inequalities of complex numbers in the order where $z\le w$ means $w-z$ is real and nonnegative.
--
--   Differences from the source:
--   - generalization: clause 2 for D = Diag(λ₁,…,λₙ) → clause 2 for every positive definite D; reason: a diagonal matrix with positive diagonal is positive definite, so the printed case is an instance
--   - generalization: f : ℝ⁺ → ℝ⁺ → f ≥ 0 on (0,∞) (f₁, f₂ likewise); reason: weaker hypothesis than positive values; only values at ratios of positive eigenvalues enter
--   - encoding: 0 ≤ 𝕁^{f₁}_D ≤ 𝕁^{f₂}_D as operators on Mₙ → for every complex B, 0 ≤ Tr(B*𝕁^{f₁}_D B) ≤ Tr(B*𝕁^{f₂}_D B) in ComplexOrder; reason: definition of the operator order with the Hilbert–Schmidt inner product
--   - encoding: Mₙ → complex matrices over a finite index type; reason: Lean convention, same instances
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, Lemma 1.1, p.7

import Mathlib
import Definitions.Def_PetzFisher_JMap

open scoped Matrix ComplexOrder

namespace PetzFisher

/-- Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, Lemma 1.1, p.7:
"Assume that `f : ℝ⁺ → ℝ⁺` is continuous and `D = Diag(λ₁, λ₂, …, λₙ)`. Then
`(𝕁^f_D B)_{ij} = λ_j f(λ_i/λ_j) B_{ij}`. Moreover, if `f₁ ≤ f₂`, then `0 ≤ 𝕁^{f₁}_D ≤ 𝕁^{f₂}_D`."

Clause (a) is the entrywise formula for a diagonal `D` with positive diagonal (`D` positive
invertible, the standing assumption of §1.2, p.7). Clause (b) is the operator order on `Mₙ` with
the Hilbert–Schmidt inner product `⟨X, Y⟩ = Tr Xᴴ Y`: for every complex matrix `B`,
`0 ≤ ⟨B, 𝕁^{f₁}_D B⟩ ≤ ⟨B, 𝕁^{f₂}_D B⟩`, the inequalities taken in `ℂ` with `ComplexOrder` (so they
also assert that the traces are real).

**Formalization Note.** `f : ℝ⁺ → ℝ⁺` is a function `ℝ → ℝ` that is continuous and nonnegative on
`(0, ∞)`; `f₁ ≤ f₂` is pointwise on `(0, ∞)`. Clause (b) is stated for every positive definite `D`,
not only diagonal ones; it specializes to the printed diagonal case. -/
theorem lemma_1_1_diagonal_form_and_order {I : Type} [Fintype I] [DecidableEq I] :
    (∀ (f : ℝ → ℝ), ContinuousOn f (Set.Ioi 0) → (∀ x : ℝ, 0 < x → 0 ≤ f x) →
      ∀ (lam : I → ℝ), (∀ i, 0 < lam i) → ∀ (B : Matrix I I ℂ) (i j : I),
        JMap f (Matrix.diagonal (fun a => ((lam a : ℝ) : ℂ))) B i j =
          (((lam j * f (lam i / lam j)) : ℝ) : ℂ) * B i j) ∧
    (∀ (f₁ f₂ : ℝ → ℝ), ContinuousOn f₁ (Set.Ioi 0) → ContinuousOn f₂ (Set.Ioi 0) →
      (∀ x : ℝ, 0 < x → 0 ≤ f₁ x) → (∀ x : ℝ, 0 < x → 0 ≤ f₂ x) →
      (∀ x : ℝ, 0 < x → f₁ x ≤ f₂ x) →
      ∀ (D : Matrix I I ℂ), D.PosDef → ∀ (B : Matrix I I ℂ),
        0 ≤ (Bᴴ * JMap f₁ D B).trace ∧ (Bᴴ * JMap f₁ D B).trace ≤ (Bᴴ * JMap f₂ D B).trace) := by sorry

end PetzFisher
