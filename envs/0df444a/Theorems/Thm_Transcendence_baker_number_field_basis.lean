-- Prove2me | Theorems.Thm_Transcendence_baker_number_field_basis
-- name    : Transcendence.baker_number_field_basis
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:14:01.308263+00:00
-- url     : https://prove2.me/theorems/46da3787-b843-4ab8-8c3d-1c627a7847aa
-- title:
--   If Σ β_k ℓ_k is algebraic for a ℚ-basis (β_k) of a number field and logarithms ℓ_k, every ℓ_k is 0
-- statement:
--   Let $K \subset \mathbb{C}$ be a number field, $(\beta_k)$ a basis of $K$ over $\mathbb{Q}$, and $\ell_k$ logarithms of algebraic numbers. If $\sum_k \beta_k\ell_k$ is algebraic, then every $\ell_k = 0$.
--
--   This is Theorem 4.5 of Waldschmidt's book. The matrix $(\sigma(\beta_k))$ of the embeddings is invertible by the non-degeneracy of the trace form; with $\lambda_\sigma = \sum_k \sigma(\beta_k)\ell_k$, the criterion of Schneider–Lang (`Transcendence.schneider_lang_cartesian`, the book's Corollary 4.2) is applied on the coordinates where $\lambda_\sigma \ne 0$: with $d_0 = 1$ when $\lambda_\sigma \ne 0$ at the inclusion $K \subset \mathbb{C}$, and with $d_0 = 0$ otherwise. The book splits instead by whether some, none or all of the $\lambda_\sigma$ vanish.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None. The contribution of this node is the formal proof. A step the book leaves implicit is written out: the invertibility used in its third case.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Theorem 4.5 with Lemma 4.6 (pp. 119–121), §4.2.4; the route is D. Bertrand and D. W. Masser, Linear forms in elliptic integrals, Invent. Math. 58 (1980), 283–288; D. W. Masser, A note on Baker's theorem, in Recent Progress in Analytic Number Theory, Vol. 2 (Durham, 1979), Academic Press, 1981, 153–158. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **Baker's theorem over a basis of a number field** (Waldschmidt, *Diophantine Approximation on Linear
Algebraic Groups*, Th. 4.5, proved in §4.2.4 from Cor. 4.3 and Cor. 4.4). Let `K ⊂ ℂ` be a number field,
`(β_k)` a basis of `K` over `ℚ`, and `ℓ_k` logarithms of algebraic numbers (each `e^{ℓ_k}` algebraic). If
`β₁ℓ₁ + ⋯ + β_dℓ_d` is algebraic, then every `ℓ_k` is `0`. -/
theorem baker_number_field_basis (K : IntermediateField ℚ ℂ) {ι : Type*} [Fintype ι]
    (β : Module.Basis ι ℚ K) (ℓ : ι → ℂ) (hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k)))
    (hsum : IsAlgebraic ℚ (∑ k, (β k : ℂ) * ℓ k)) : ∀ k, ℓ k = 0 := by
  sorry

end Transcendence
