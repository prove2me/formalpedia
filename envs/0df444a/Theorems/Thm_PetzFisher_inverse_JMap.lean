-- Prove2me | Theorems.Thm_PetzFisher_inverse_JMap
-- name    : PetzFisher.inverse_JMap
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:12.958868+00:00
-- url     : https://prove2.me/theorems/5637cad0-b6a3-4105-b8d5-db55350ce66f
-- title:
--   The inverse of $\mathbb J^f_D$ is $(1/f)(\mathbb L_D\mathbb R_D^{-1})\mathbb R_D^{-1}$, acting as $B\mapsto Y\circ B$, $Y_{ij}=1/m_f(\lambda_i,\lambda_j)$
-- statement:
--   Let $f$ be positive on $(0,\infty)$, let $D\in M_n$ be positive definite, and write $m_f(x,y)=y\,f(x/y)$ for the mean associated with $f$. Then:
--
--   1. the mapping $(\mathbb J^f_D)^{-1}=\dfrac1f(\mathbb L_D\mathbb R_D^{-1})\,\mathbb R_D^{-1}$ is a two-sided inverse of $\mathbb J^f_D$: for every $B\in M_n$,
--   $$
--   (\mathbb J^f_D)^{-1}\big(\mathbb J^f_D B\big)=B,\qquad \mathbb J^f_D\big((\mathbb J^f_D)^{-1}B\big)=B;
--   $$
--   2. for $D=\mathrm{Diag}(\lambda_1,\dots,\lambda_n)$ with all $\lambda_i>0$ it acts as the Hadamard product $B\mapsto Y\circ B$ with
--   $$
--   Y_{ij}=\frac1{m_f(\lambda_i,\lambda_j)}=\frac1{\lambda_j f(\lambda_i/\lambda_j)} .
--   $$
--
--   The inverse $(\mathbb J^f_D)^{-1}$ defines the monotone metric $\gamma^f_D(A,B)=\operatorname{Tr}A\,(\mathbb J^f_D)^{-1}(B)$ and the Fisher information matrix.
--
--   **Formalization Note** $(1/f)(\mathbb L_D\mathbb R_D^{-1})\mathbb R_D^{-1}$ is the published `inverseMetric f D`, i.e. $B\mapsto\sum_{u,v}(v f(u/v))^{-1}P_uBP_v$ over the distinct eigenvalues $u,v$ of $D$.
--
--   Differences from the source:
--   - generalization: f a standard operator monotone function → f positive on (0,∞); reason: every standard f is positive on (0,∞) (2x/(x+1) ≤ f(x), p.8), so the printed case is an instance
--   - reading: B ↦ Y ∘ B with Y_ij = 1/m_f(λ_i, λ_j) → the Hadamard form stated for diagonal D = Diag(λ₁,…,λₙ), λ_i > 0; reason: the λ_i are the eigenvalues of D and the Hadamard form refers to its eigenbasis, as in Lemma 1.1 and (12)
--   - encoding: "the inverse of 𝕁^f_D" → left- and right-inverse identities for every B; reason: definition of the inverse of a linear map
-- source:
--   Petz–Ghinea, Introduction to quantum Fisher information, arXiv:1008.2417v1, §1.2, p.8 (unnumbered display after (12))

import Mathlib
import Definitions.Def_PetzFisher_JMap

open scoped Matrix ComplexOrder

namespace PetzFisher

/-- Petz–Ghinea, *Introduction to quantum Fisher information*, arXiv:1008.2417v1, §1.2, p.8
(unnumbered): "The inverse of `𝕁^f_D` is the mapping `(1/f)(𝕃_D ℝ_D^{-1}) ℝ_D^{-1}` which acts as
`B ↦ Y ∘ B` with `Y_{ij} = 1/m_f(λ_i, λ_j)`", where `m_f(x, y) = y f(x/y)` (p.8, above (12)).

Three clauses: for `f` positive on `(0, ∞)` and `D` positive definite, the published
`inverseMetric f D` (the mapping `(1/f)(𝕃_D ℝ_D^{-1}) ℝ_D^{-1}`) is a left and a right inverse of
`𝕁^f_D`; and for diagonal `D = Diag(λ₁, …, λₙ)` with `λ_i > 0` it acts entrywise as
`B_{ij} ↦ B_{ij} / (λ_j f(λ_i/λ_j))`.

**Formalization Note.** The page states this for the standard operator monotone functions of §1.2;
only positivity of `f` on `(0, ∞)` is assumed here, which every standard function has
(`2x/(x+1) ≤ f(x)`, p.8). -/
theorem inverse_JMap {I : Type} [Fintype I] [DecidableEq I] (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 0 < x → 0 < f x) :
    (∀ (D : Matrix I I ℂ), D.PosDef → ∀ B : Matrix I I ℂ,
      QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f D (JMap f D B) = B ∧
      JMap f D (QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f D B) = B) ∧
    (∀ (lam : I → ℝ), (∀ i, 0 < lam i) → ∀ (B : Matrix I I ℂ) (i j : I),
      QAlgorithms.Papers.Independent.Bridge50.P31.inverseMetric f
          (Matrix.diagonal (fun a => ((lam a : ℝ) : ℂ))) B i j =
        ((((lam j * f (lam i / lam j)) : ℝ) : ℂ))⁻¹ * B i j) := by sorry

end PetzFisher
