-- Prove2me | Theorems.Thm_QaryCVP_lemma_4_4
-- name    : QaryCVP.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:08.3312+00:00
-- url     : https://prove2.me/theorems/7ac9c25e-63c3-4367-9f7c-f902d9e15a47
-- title:
--   Lemma 4.4 — average success to every right-hand side, except a fraction (19) of $(C_0,C_1)$
-- statement:
--   Let $G$ be a finite abelian group of size $M$, $n_0\ge1$, $A:\mathbb Z^{n_0}\to G$ a homomorphism and $B\ge0$. Let a randomized procedure $S(A,t)$ return $\bot$ or $v\in\mathbb Z^{n_0}$ with $Av=t$ and $\|v\|\le B$, with average success probability at least $p>0$ over uniform $t\in G$ and its randomness. Let $\ell,\ell'\ge1$ and $C_0\in G^\ell$, $C_1\in G^{\ell'}$ with independent uniform columns. An attempt for $s\in G$ samples independent uniform $u\in\{0,1\}^\ell$, $j\in[\ell']$, $\sigma\in\{-1,1\}$, calls $v\leftarrow S(A,\sigma(s-C_0u-C_1e_j))$ with independent randomness, and on success returns $w=(\sigma v^\top,u^\top,e_j^\top)^\top$. Fix $L>0$, $0<\eta<p$, $0<\theta<1$, $\alpha>0$, and put $\xi=\min\{1,\alpha/\eta^2\}$, $p_*=(1-\theta)(p-\eta)$.
--
--   1. Except for a fraction of pairs $(C_0,C_1)$ at most
--
--   $$(1+B^2/L^2)\frac{2^{-\ell}}{\alpha}+M\binom{\ell'}{\lceil\theta\ell'\rceil}\xi^{\lceil\theta\ell'\rceil},\qquad(19)$$
--
--   every $s\in G$ simultaneously satisfies $\Pr[\text{success}]\ge p_*$ and $\|\mathbb E[w\mid\text{success}]\|\le(\eta L+\theta B+\sqrt{\ell+1})/p_*$.
--   2. Every successful output satisfies $[A\ C_0\ C_1]w=s$ and $\|w\|^2\le B^2+\ell+1$.
--   3. If the average-success property holds only for a random $A$ and fails with probability $\zeta$, then $\zeta$ is added to (19).
--
--   **Formalization Note** The procedure is a randomized function on a probability space $(\Omega,\mu)$ with measurable outcome events. In clause 3 the random instance ranges over a finite set with an arbitrary law $\pi$, independent of $(C_0,C_1)$, and each instance carries its homomorphism and its procedure.
--
--   Differences from the source:
--   - generalization: a randomized procedure (unspecified randomness) → a randomized function S t ω on an arbitrary probability space (Ω, μ) with measurable outcome events; reason: covers every source of randomness; fair coins are a special case
--   - generalization: a random A → a random instance with an arbitrary law π on a finite set, carrying A and S; reason: covers the uniform matrix law used later
--   - encoding: An attempt makes one call to S and otherwise uses polynomially many group operations → not a separate clause: the attempt is defined (grpAttempt) as one call of S plus group operations; reason: the operation count is a property of the construction in this model, not a claim about a machine
--   - encoding: fraction of matrices → count of matrices with the property divided by q^{mn}, as a real number; reason: R5; same instances
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.4 and (19), p.36

import Mathlib
import Definitions.Def_QaryCVP_corrAttempt

open MeasureTheory ProbabilityTheory

namespace QaryCVP

open Classical in
/-- **Lemma 4.4** (average success to every right-hand side). Kim, Kwon, Lee, Lee, STOC 2027
submission manuscript (sha256 9aeb2ff4…ab4), Lemma 4.4 and (19), p.36.

Let `G` be a finite abelian group of size `M`, `n₀ ≥ 1`, `A : Z^{n₀} → G` a homomorphism and
`B ≥ 0`. Let `S(A, t)` be a randomized procedure (randomness `ω ∼ μ`) returning `⊥` or `v ∈ Z^{n₀}`
with `Av = t`, `‖v‖ ≤ B`, whose average success probability over uniform `t ∈ G` and its
randomness is at least `p > 0`. Let `ℓ, ℓ′ ≥ 1` and `C₀ ∈ G^ℓ`, `C₁ ∈ G^{ℓ′}` with independent
uniform columns. An attempt for `s ∈ G` samples independent uniform `u ∈ {0,1}^ℓ`, `j ∈ [ℓ′]`,
`σ ∈ {−1, 1}`, calls `v ← S(A, σ(s − C₀u − C₁e_j))` with independent randomness and on success
returns `w = (σv, u, e_j)`. Fix `L > 0`, `0 < η < p`, `0 < θ < 1`, `α > 0`, put
`ξ = min{1, α/η²}`, `p* = (1 − θ)(p − η)`. Then:

1. except for a fraction of pairs `(C₀, C₁)` at most
   `(1 + B²/L²) 2^{−ℓ}/α + M (ℓ′ choose ⌈θℓ′⌉) ξ^{⌈θℓ′⌉}` (19), every `s ∈ G` simultaneously
   satisfies `Pr[success] ≥ p*` and `‖E[w | success]‖ ≤ (ηL + θB + √(ℓ + 1))/p*`;
2. every successful output satisfies `[A C₀ C₁]w = s` and `‖w‖² ≤ B² + ℓ + 1`;
3. if the average-success property holds only for a random `A` (with any law `π` on a finite set
   of instances, independent of `C₀, C₁`) and fails with probability at most `ζ`, the exceptional
   probability of the triple `(A, C₀, C₁)` is at most (19) `+ ζ`.

**Formalization Note.** The procedure is a randomized function `S t ω` on a probability space
`(Ω, μ)`; its outcome events are measurable. "An attempt makes one call to S and otherwise uses
polynomially many group operations" holds by the definition of `grpAttempt` (one call of `S`). In
clause 3 the instance `a` carries its homomorphism `A a` and its procedure `S a`. -/
theorem lemma_4_4 {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (n0 : ℕ) (hn0 : 1 ≤ n0)
    (B : ℝ) (hB : 0 ≤ B) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (ℓ ℓ' : ℕ) (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') (L η θ α : ℝ) (hL : 0 < L)
    (hη : 0 < η) (hηp : η < p) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hα : 0 < α) :
    let ξ : ℝ := min 1 (α / η ^ 2)
    let pst : ℝ := (1 - θ) * (p - η)
    let M : ℝ := Fintype.card G
    let bnd19 : ℝ := (1 + B ^ 2 / L ^ 2) * (1 / 2 : ℝ) ^ ℓ / α +
      M * (ℓ'.choose ⌈θ * ℓ'⌉₊ : ℝ) * ξ ^ ⌈θ * ℓ'⌉₊
    let Good : (G → Ω → Option (Fin n0 → ℤ)) → (Fin ℓ → G) → (Fin ℓ' → G) → Prop :=
      fun S C0 C1 => ∀ s : G,
        pst ≤ succProb (attMeasure ℓ ℓ' μ) (grpAttempt S C0 C1 s) ∧
        condMeanNorm (attMeasure ℓ ℓ' μ) (grpAttempt S C0 C1 s) ≤
          (η * L + θ * B + Real.sqrt (ℓ + 1)) / pst
    (∀ (A : (Fin n0 → ℤ) →+ G) (S : G → Ω → Option (Fin n0 → ℤ)),
      (∀ t (o : Option (Fin n0 → ℤ)), MeasurableSet {ω | S t ω = o}) →
      (∀ t ω v, S t ω = some v → A v = t ∧ ∑ i, ((v i : ℝ)) ^ 2 ≤ B ^ 2) →
      p ≤ (∑ t, (μ {ω | (S t ω).isSome}).toReal) / M →
      (1 - bnd19 ≤
          ((Finset.univ.filter (fun CC : (Fin ℓ → G) × (Fin ℓ' → G) => Good S CC.1 CC.2)).card : ℝ) /
            M ^ (ℓ + ℓ')) ∧
      (∀ (C0 : Fin ℓ → G) (C1 : Fin ℓ' → G) (s : G) (a : AttSample ℓ ℓ' Ω)
          (w : Fin n0 ⊕ (Fin ℓ ⊕ Fin ℓ') → ℤ), grpAttempt S C0 C1 s a = some w →
        A (fun k => w (Sum.inl k)) + (∑ k, w (Sum.inr (Sum.inl k)) • C0 k) +
            (∑ k, w (Sum.inr (Sum.inr k)) • C1 k) = s ∧
          ∑ i, ((w i : ℝ)) ^ 2 ≤ B ^ 2 + ℓ + 1)) ∧
    (∀ (𝒜 : Type) [Fintype 𝒜] (π : 𝒜 → ℝ), (∀ a, 0 ≤ π a) → ∑ a, π a = 1 →
      ∀ (A : 𝒜 → (Fin n0 → ℤ) →+ G) (S : 𝒜 → G → Ω → Option (Fin n0 → ℤ)) (ζ : ℝ),
      (∀ a t (o : Option (Fin n0 → ℤ)), MeasurableSet {ω | S a t ω = o}) →
      (∀ a t ω v, S a t ω = some v → A a v = t ∧ ∑ i, ((v i : ℝ)) ^ 2 ≤ B ^ 2) →
      (∑ a, π a * (if p ≤ (∑ t, (μ {ω | (S a t ω).isSome}).toReal) / M then 0 else 1)) ≤ ζ →
      (∑ a, π a * (1 - ((Finset.univ.filter
          (fun CC : (Fin ℓ → G) × (Fin ℓ' → G) => Good (S a) CC.1 CC.2)).card : ℝ) /
            M ^ (ℓ + ℓ'))) ≤ bnd19 + ζ) := by sorry

end QaryCVP
