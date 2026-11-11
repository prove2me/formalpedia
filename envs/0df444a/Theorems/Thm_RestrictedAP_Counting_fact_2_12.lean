-- Prove2me | Theorems.Thm_RestrictedAP_Counting_fact_2_12
-- name    : RestrictedAP.Counting.fact_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:53.960206+00:00
-- url     : https://prove2.me/theorems/d60f633f-2550-4e6a-9227-e9d8dad8f9c9
-- title:
--   Fact 2.12 — discrete product functions far from constant have exponentially small mean and noisy 2-norm
-- statement:
--   Let $\Sigma$ be a finite alphabet, $\nu$ a distribution on $\Sigma$ in which every atom has probability at least $\alpha>0$, and $P:\Sigma^n\to\mathbb D$ an $M$-discrete (normalized) product function with $\Delta_{\rm symbolic}(P,1)\ge D$. Then:
--
--   1. there is $c=c(\alpha,M)>0$, independent of $\Sigma,\nu,n,P,D$, with $$\Big|\mathbb E_{x\sim\nu^{\otimes n}}[P(x)]\Big|\le 2^{-cD};$$
--   2. for every $\tau\in(0,1]$ there is $c=c(\alpha,\tau,M)>0$ with $\|T^{\otimes n}_{1-\tau,\nu}P\|_{L^2(\nu^{\otimes n})}\le2^{-cD}$.
--
--   This is the basic estimate behind the quasirandomness of high-rank collections (Lemmas 3.5, 3.7, 3.8): a product function that differs from a constant in many coordinates has small mean and is almost killed by noise.
--
--   Differences from the source:
--   - reading: 2^{−Ω_{α,M}(D)} and 2^{−Ω_{α,τ,M}(D)} → ∃ c > 0 depending only on (α, M), resp. (α, τ, M), quantified before Σ, ν, n, P, D; bound 2^{−c·D}; reason: §2 notation: the hidden constant depends only on the subscripts
--   - reading: 'the probability of each atom is at least α' with an Ω_α constant → 0 < α; reason: α is a lower bound on atom probabilities and the constant is a function of α; for α ≤ 0 the hypothesis is void and the bound fails for a point mass
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - reading: for all τ > 0 → τ ∈ (0, 1]; reason: T_{1−τ} is defined (Definition 2.6) only for 1 − τ ∈ [0, 1]
--   - encoding: ord(P) ∈ ℕ ∪ {∞} → `orderOf P` in the monoid of functions (0 encodes ∞); M-discrete = 0 < orderOf P ≤ M; reason: Mathlib's order of an element is the least k ≥ 1 with P^k = 1, as Definition 2.3
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 9, Fact 2.12

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators

namespace RestrictedAP.Counting

/-- **Fact 2.12** (p. 9). Let `P : Σ^n → D` be an `M`-discrete (normalized) product function and
`ν` a distribution on `Σ` all of whose atoms have probability at least `α > 0`, and suppose
`Δ_symbolic(P, 1) ≥ D`. Then
1. `|E_{x ∼ ν^{⊗n}} P(x)| ≤ 2^{−c D}` with `c = c(α, M) > 0`;
2. for every `τ ∈ (0, 1]`, `‖T^{⊗n}_{1−τ} P‖₂ ≤ 2^{−c D}` with `c = c(α, τ, M) > 0`
   (noise operator and `L²` norm with respect to `ν`). -/
theorem fact_2_12 :
    (∀ (M : ℕ) (α : ℝ), 0 < α → ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (P : (Fin n → Sig) → ℂ) (D : ℤ),
        IsDist ν → AtomsAtLeast ν α → IsProductFunction σs P → IsDiscrete M P →
        (D : ℝ) ≤ (symbolicDist P 1 : ℝ) →
        ‖expectC (tensorPow ν n) P‖ ≤ (2 : ℝ) ^ (-(c * D))) ∧
    (∀ (M : ℕ) (α τ : ℝ), 0 < α → 0 < τ → τ ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (P : (Fin n → Sig) → ℂ) (D : ℤ),
        IsDist ν → AtomsAtLeast ν α → IsProductFunction σs P → IsDiscrete M P →
        (D : ℝ) ≤ (symbolicDist P 1 : ℝ) →
        l2Norm (tensorPow ν n) (noiseOp ν (1 - τ) n P) ≤ (2 : ℝ) ^ (-(c * D))) := by sorry

end RestrictedAP.Counting
