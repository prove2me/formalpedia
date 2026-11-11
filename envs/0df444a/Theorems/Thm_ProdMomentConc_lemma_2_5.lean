-- Prove2me | Theorems.Thm_ProdMomentConc_lemma_2_5
-- name    : ProdMomentConc.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:16.674391+00:00
-- url     : https://prove2.me/theorems/f91e0c9b-d708-4860-ab51-bc1b694ea0fb
-- title:
--   Lemma 2.5 — product inequality for nonnegative read-$\Delta$ families
-- statement:
--   Let $X_1,\dots,X_m$ be mutually independent Boolean random variables. For each $i \in [n]$ let $P_i \subseteq [m]$ and let $F_i = f_i(X_{P_i}) \ge 0$ be a nonnegative function of the variables indexed by $P_i$. Suppose the family is **read-$\Delta$**: every $j \in [m]$ lies in at most $\Delta$ of the sets $P_i$, where $\Delta \ge 1$. Then
--
--   $$
--   \mathbb E\Big[\prod_{i=1}^n F_i\Big] \le \Big(\prod_{i=1}^n \mathbb E\big[F_i^{\Delta}\big]\Big)^{1/\Delta}.
--   $$
--
--   This is the read-$\Delta$ inequality of Gavinsky et al. in the exponential-moment form of Duppala et al. (a case of Finner's inequality). Applied to $F_i = e^{\lambda Y_i}$ it gives the read-$\Delta$ Chernoff exponent $n/\Delta$, and it is the step of the mission where independence of the underlying bits is used.
--
--   **Formalization Note** The bits are `Bool`-valued and mutually independent (`iIndepFun`). Each $f_i$ is a real-valued nonnegative function of the restriction of the bit vector to $P_i$; it takes finitely many values, so every expectation exists.
--
--   Differences from the source:
--   - reading: "nonnegative read-Δ family" (Definition 2.4 has values in [0,1]) → fᵢ real-valued and nonnegative, unbounded above; reason: the lemma says "nonnegative" and is applied to Fᵢ = exp(λYᵢ) > 1 (p.4, proof of Theorem 3.1)
--   - encoding: Δ a positive integer implicitly → hypothesis 1 ≤ Δ; reason: 1/Δ is undefined for Δ = 0
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), Lemma 2.5 ([Dup+25]), p.9 (PDF p.9), with Definition 2.4, p.9

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ProdMomentConc

/-- **Lemma 2.5 (read-Δ product inequality, [Dup+25]).**
Saks, Srinivasan, Valieva, *Concentration from Product Moments via an Additional Element of
Randomness*, arXiv:2608.04125 (held version, sha256 5218e9d0…), Lemma 2.5, p.9.

Let `F₁, …, Fₙ` be a nonnegative read-`Δ` family over independent Boolean random variables
`X₁, …, Xₘ`. Then `E[∏ⱼ Fⱼ] ≤ (∏ⱼ E[Fⱼ^Δ])^{1/Δ}`.

**Formalization Note.**
* As in Definition 2.4 (p.9), `Fᵢ = fᵢ(X_{Pᵢ})` for a set `Pᵢ ⊆ [m]` and a function `fᵢ` of the bits
  in `Pᵢ`; here `fᵢ` is real-valued and nonnegative ("nonnegative read-∆ family"; the lemma is
  applied to `Fᵢ = exp(λYᵢ)`, which exceeds `1`).
* Read-`Δ`: each `j ∈ [m]` lies in at most `Δ` of the sets `Pᵢ`; `1 ≤ Δ` so that `1/Δ` is defined.
* The bits are `Bool`-valued and mutually independent (`iIndepFun`); every `Fᵢ` then takes finitely
  many values, so all expectations exist. -/
theorem lemma_2_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m n : ℕ} (X : Fin m → Ω → Bool) (hXm : ∀ j, Measurable (X j)) (hX : iIndepFun X μ)
    (P : Fin n → Finset (Fin m)) (F : (i : Fin n) → (P i → Bool) → ℝ)
    (hF : ∀ i b, 0 ≤ F i b) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ P i)).card ≤ Δ) :
    ∫ ω, ∏ i, F i (fun j => X j ω) ∂μ ≤
      (∏ i, ∫ ω, F i (fun j => X j ω) ^ Δ ∂μ) ^ (1 / (Δ : ℝ)) := by sorry

end ProdMomentConc
