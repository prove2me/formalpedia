-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_proposition_3_9
-- name    : RSBeyondJohnson.FirstOrder.proposition_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:31.264358+00:00
-- url     : https://prove2.me/theorems/37d57237-adbc-4383-9e54-3e78d0c33565
-- title:
--   Proposition 3.9 — global interpolation principle
-- statement:
--   Let $\alpha_1,\dots,\alpha_n\in F$ be distinct, $y\in F^n$, $1\le A\le n$, and let $\mathcal Q\subseteq F[X,Y_0,\dots,Y_d]$ be a finite-dimensional subspace. For each received pair $(\alpha_i,y_i)$ let $\Phi_i$ be a linear map on $\mathcal Q$ such that $Q\in\ker\Phi_i$ and $P(\alpha_i)=y_i$ imply $(X-\alpha_i)^m\mid Q(X,P,P^{[1]},\dots,P^{[d]})$. Assume every $Q\in\mathcal Q$ specializes at every polynomial of degree $\le D$ to a polynomial of degree $<mA$. If
--   $$\dim\mathcal Q>\sum_{i=1}^n\operatorname{rank}\Phi_i,$$
--   then $\mathcal Q$ contains an explainer for $y$ at degree bound $D+1$ and agreement threshold $A$: a nonzero $Q$ with $Q(X,P,P^{[1]},\dots,P^{[d]})\equiv0$ for every $P$ of degree $\le D$ agreeing with $y$ in at least $A$ positions. This is the Guruswami–Sudan dimension argument in hidden-derivative form; each later construction only bounds dimension, local ranks and specialization degree.
--
--   Differences from the source:
--   - encoding: positions 1, …, n; distinct evaluation points α_1, …, α_n → Fin n (0-based); α : Fin n → F with Function.Injective α; reason: Lean indexing; the same instances
--   - reading: Proposition 3.9 states no condition on the points, on A or on m → α injective, 1 ≤ A ≤ n and 1 ≤ m are hypotheses; reason: distinct points and 1 ≤ A ≤ n are the standing context of Definition 3.8 (explainer), the conclusion's notion: 'Fix … distinct evaluation points …, integers K ≥ 1 and 1 ≤ A ≤ n'; m ≥ 1 is the standing assumption of §3.2, p. 18: 'Fix an order d ≥ 0 and a target multiplicity m ≥ 1'
--   - encoding: linear maps Φ_i on 𝒬 and rank Φ_i → Φ i : 𝒬 →ₗ[F] M i into arbitrary F-modules; rank = finrank of LinearMap.range; reason: the paper leaves the codomain unspecified
--   - encoding: degree-≤ D polynomial; specializes to degree less than mA → P.natDegree ≤ D (zero polynomial included); (hasseJetEval d Q P).degree < m·A; reason: same polynomials; degree of 0 is ⊥
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 19, Proposition 3.9

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Proposition 3.9 (Global interpolation principle)**, p. 19. Let `𝒬 ⊆ F[X, Y₀, …, Y_d]` be
finite dimensional and `Φ_i` linear maps on `𝒬`, one for each received pair `(α_i, y_i)`, such
that `Q ∈ ker Φ_i` and `P(α_i) = y_i` imply `(X − α_i)^m ∣ Q(X, P, P^[1], …, P^[d])`. If every
`Q ∈ 𝒬` specializes at every polynomial of degree `≤ D` to degree `< mA` and
`dim 𝒬 > ∑_i rank Φ_i`, then `𝒬` contains an explainer for `y` at degree bound `D + 1` and
agreement threshold `A`. (`m ≥ 1` is the standing "target multiplicity" of §3.2, p. 18;
distinct points and `1 ≤ A ≤ n` are the context of Definition 3.8.) -/
theorem proposition_3_9 {F : Type*} [Field F] {n : ℕ} (α y : Fin n → F)
    (hα : Function.Injective α) (d m D A : ℕ) (hm : 1 ≤ m) (hA1 : 1 ≤ A) (hAn : A ≤ n)
    (𝒬 : Submodule F (MvPolynomial (Option (Fin (d + 1))) F)) [FiniteDimensional F 𝒬]
    {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    (Φ : ∀ i, 𝒬 →ₗ[F] M i)
    (hΦ : ∀ (i : Fin n) (Q : 𝒬), Φ i Q = 0 → ∀ P : F[X], P.eval (α i) = y i →
      (X - C (α i)) ^ m ∣ RSListDecodingCapacity.AllRates.hasseJetEval d (Q : MvPolynomial _ F) P)
    (hspec : ∀ Q ∈ 𝒬, ∀ P : F[X], P.natDegree ≤ D →
      (RSListDecodingCapacity.AllRates.hasseJetEval d Q P).degree < ((m * A : ℕ) : WithBot ℕ))
    (hdim : ∑ i, Module.finrank F (LinearMap.range (Φ i)) < Module.finrank F 𝒬) :
    ∃ Q ∈ 𝒬, IsExplainer α y (D + 1) A d Q := by sorry

end RSBeyondJohnson.FirstOrder
