-- Prove2me | Theorems.Thm_PrivBayesTest_lemma_C_1
-- name    : PrivBayesTest.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:07.509891+00:00
-- url     : https://prove2.me/theorems/43363cce-9b4e-4bbf-94bc-7dafdbce2dd2
-- title:
--   Lemma C.1 (saddle points and balancing) for $\Phi(\alpha,z)=\alpha A(z)+(1-\alpha)B(z)+\omega(\alpha)\varepsilon W(z)$
-- statement:
--   Fix $\varepsilon>0$ and let $\omega(\alpha)$ be either $\tilde\alpha=\min\{\alpha,1-\alpha\}$ or $\alpha$. Let $Z$ be a nonempty convex subset of a real vector space with a topology, let $A,B,W$ be nonnegative, convex and lower semicontinuous functions on $Z$, and set
--
--   $$
--   \Phi(\alpha,z)=\alpha A(z)+(1-\alpha)B(z)+\omega(\alpha)\,\varepsilon\,W(z).
--   $$
--
--   Suppose that every sublevel set $\{z\in Z:\max_{\alpha\in[0,1]}\Phi(\alpha,z)\le t\}$ is compact. Then:
--
--   1. $\Phi$ has a saddle point $(\alpha^*,z^*)\in[0,1]\times Z$: $z^*$ minimizes $\Phi(\alpha^*,\cdot)$ over $Z$ and $\alpha^*$ maximizes $\Phi(\cdot,z^*)$ over $[0,1]$;
--   2. for every saddle point $(\alpha^*,z^*)$, its value $V=\Phi(\alpha^*,z^*)$ equals $\sup_{\alpha\in[0,1]}\inf_{z\in Z}\Phi(\alpha,z)$, and if $\alpha^*\in(0,1)$ there is $\tau\in[0,1]$ with
--   $$
--   V \;=\; A(z^*)+\tau\varepsilon W(z^*) \;=\; B(z^*)+(1-\tau)\varepsilon W(z^*),
--   $$
--   where moreover $\tau\in\{0,1\}$ if $\omega=\tilde\alpha$ and $\alpha^*\ne1/2$, and $\tau=1$ if $\omega(\alpha)=\alpha$.
--
--   The lemma gives the balancing value $\tau$ used in the converse (Lemma 3.2) through Corollary C.2.
--
--   Differences from the source:
--   - encoding: z ranging over a convex set Z → Z a nonempty convex subset of a real vector space E with an arbitrary topology; reason: the topology is needed for lower semicontinuity and compactness; Z = ∅ is the degenerate case in which no saddle point exists and the statement has no content
--   - encoding: z ↦ max_{α∈[0,1]} Φ(α, z) has compact sublevel sets → {z ∈ Z | ∀ α ∈ [0,1], Φ(α, z) ≤ t} is compact for every real t; reason: same sets
--   - generalization: the value and τ clauses for the saddle point the lemma produces → the value and τ clauses for every saddle point; reason: contains the printed claim
--   - encoding: sup_α inf_z Φ(α, z) → extended-real supremum over α ∈ [0,1] of the infimum over z ∈ Z; reason: Lean convention; α ranges over [0,1] as in the lemma's max
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Lemma C.1 and eq. (7), p.28

import Mathlib
import Definitions.Def_PrivBayesTest_saddleObj
import Definitions.Def_PrivBayesTest_klTvValue

namespace PrivBayesTest

/-- **Lemma C.1 (Saddle Points and Balancing)** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), p.28. Fix `ε > 0` and let `ω` be either
`α̃ = min{α, 1 − α}` or `α`. For nonnegative functions `A, B, W` on a convex set `Z` let
`Φ(α, z) = α A(z) + (1 − α) B(z) + ω(α) ε W(z)` (eq. (7)). Suppose `A, B, W` are convex and lower
semicontinuous and `z ↦ max_{α∈[0,1]} Φ(α, z)` has compact sublevel sets. Then `Φ` has a saddle point
`(α*, z*)` (`z*` minimizes `Φ(α*, ·)` over `Z` and `α*` maximizes `Φ(·, z*)` over `[0,1]`), and its
value `V = Φ(α*, z*)` equals `sup_α inf_z Φ(α, z)`. If `α* ∈ (0,1)`, there is `τ ∈ [0,1]` with
`V = A(z*) + τ ε W(z*) = B(z*) + (1 − τ) ε W(z*)`; moreover `τ ∈ {0,1}` if `ω = α̃` and `α* ≠ 1/2`, and
`τ = 1` if `ω(α) = α`.

**Formalization Note** `Z` is a convex subset of a real vector space `E` carrying an arbitrary
topology (used for lower semicontinuity and compactness only). `Z` is assumed nonempty. The
sublevel set `{z ∈ Z | max_α Φ(α, z) ≤ t}` is written `{z ∈ Z | ∀ α ∈ [0,1], Φ(α, z) ≤ t}`. The value
and the balancing clauses are stated for **every** saddle point, which contains the printed statement
about the saddle point it produces. `sup_α inf_z` is computed in `EReal` with `α ∈ [0,1]`. -/
theorem lemma_C_1 {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (ε : ℝ)
    (hε : 0 < ε) (ω : ℝ → ℝ) (hω : ω = alphaTilde ∨ ω = id) (Z : Set E) (hZ : Convex ℝ Z)
    (hZne : Z.Nonempty) (A B W : E → ℝ) (hA0 : ∀ z ∈ Z, 0 ≤ A z) (hB0 : ∀ z ∈ Z, 0 ≤ B z)
    (hW0 : ∀ z ∈ Z, 0 ≤ W z) (hAc : ConvexOn ℝ Z A) (hBc : ConvexOn ℝ Z B) (hWc : ConvexOn ℝ Z W)
    (hAl : LowerSemicontinuousOn A Z) (hBl : LowerSemicontinuousOn B Z)
    (hWl : LowerSemicontinuousOn W Z)
    (hcpt : ∀ t : ℝ, IsCompact {z ∈ Z | ∀ α ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W α z ≤ t}) :
    (∃ α₀ ∈ Set.Icc (0 : ℝ) 1, ∃ z₀ ∈ Z,
        (∀ z ∈ Z, saddleObj ω ε A B W α₀ z₀ ≤ saddleObj ω ε A B W α₀ z) ∧
        (∀ α ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W α z₀ ≤ saddleObj ω ε A B W α₀ z₀)) ∧
      ∀ α₀ ∈ Set.Icc (0 : ℝ) 1, ∀ z₀ ∈ Z,
        (∀ z ∈ Z, saddleObj ω ε A B W α₀ z₀ ≤ saddleObj ω ε A B W α₀ z) →
        (∀ α ∈ Set.Icc (0 : ℝ) 1, saddleObj ω ε A B W α z₀ ≤ saddleObj ω ε A B W α₀ z₀) →
          ((saddleObj ω ε A B W α₀ z₀ : ℝ) : EReal) =
              ⨆ α ∈ Set.Icc (0 : ℝ) 1, ⨅ z ∈ Z, ((saddleObj ω ε A B W α z : ℝ) : EReal) ∧
            (α₀ ∈ Set.Ioo (0 : ℝ) 1 → ∃ τ ∈ Set.Icc (0 : ℝ) 1,
              saddleObj ω ε A B W α₀ z₀ = A z₀ + τ * ε * W z₀ ∧
              saddleObj ω ε A B W α₀ z₀ = B z₀ + (1 - τ) * ε * W z₀ ∧
              (ω = alphaTilde → α₀ ≠ 1 / 2 → τ = 0 ∨ τ = 1) ∧
              (ω = id → τ = 1)) := by sorry

end PrivBayesTest
