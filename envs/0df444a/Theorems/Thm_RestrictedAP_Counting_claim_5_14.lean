-- Prove2me | Theorems.Thm_RestrictedAP_Counting_claim_5_14
-- name    : RestrictedAP.Counting.claim_5_14
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:21:09.482961+00:00
-- url     : https://prove2.me/theorems/89e9578d-7dfc-490f-b346-49dd67b2367e
-- title:
--   Claim 5.14 — reduction to resilient functions (as printed; false, see INSIGHTS I1)
-- statement:
--   Setting of §5.2: $\Sigma$ is a finite alphabet, $\mu$ a distribution on $\Sigma^3$ all of whose marginals equal $\nu$, with $(x,x,x)\in\mathrm{supp}(\mu)$ for every $x$, no $(\mathbb Z,+)$-embedding, and minimum non-zero atom probability $\alpha$. Fix $n$, $B\in\mathbb N$ and a function $\delta':\mathbb N\times\mathbb R\to\mathbb R$. Suppose $\Delta_1(g)\ge\delta'(B,\eta)$ for every $(B,1/2)$-resilient $g:\Sigma^n\to\{0,1\}$ with $\eta=\nu^{\otimes n}(g)$. Then for every $f:\Sigma^n\to\{0,1\}$ with $\nu^{\otimes n}(f)=\delta>0$,
--   $$\Delta_1(f)\ \ge\ \alpha^{\frac{2B}{\delta\alpha^B}}\,\delta'(B,\delta).$$
--
--   The claim is stated exactly as printed. As printed it is false (INSIGHTS I1): the hypothesis constrains $\delta'(B,\cdot)$ only at the exact densities of resilient functions, while the proof needs it at every density at least $\delta$.
--
--   Differences from the source:
--   - reading: the claim's sentence (Σ, μ, ν, α fixed by §5.2) → hypotheses: μ a distribution on Σ^3 with all marginals ν, (x, x, x) ∈ supp(μ) for every x, no (ℤ,+)-embedding, α the minimum non-zero atom probability; reason: standing assumptions of §5.2 (p. 31): the setting of Theorem 1.4 with 'the minimum non-zero probability of the distribution µ is α'
--   - encoding: ν^{⊗n}(f) = δ with the exponent 2B/(δα^B) → δ := ν^{⊗n}(f) with 0 < δ; reason: the printed bound is undefined at δ = 0
--   - encoding: g, f : Σ^n → {0, 1} → real-valued functions with g(x) ∈ {0, 1} for every x; reason: indicators as real functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 32, Claim 5.14

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience

namespace RestrictedAP.Counting

/-- **Claim 5.14** (p. 32), as printed, in the setting of §5.2: `Σ` finite, `μ` a distribution on
`Σ^3` with all marginals equal to `ν`, `(x, x, x) ∈ supp(μ)` for every `x`, no `(ℤ,+)`-embedding,
and minimum non-zero atom probability `α`. Let `B ∈ ℕ` and `δ' : ℕ × ℝ → ℝ`. Suppose
`Δ₁(g) ≥ δ'(B, η)` for every `(B, 1/2)`-resilient `g : Σ^n → {0,1}` with `η = ν^{⊗n}(g)`. Then for
every `f : Σ^n → {0,1}` with `ν^{⊗n}(f) = δ > 0`,
`Δ₁(f) ≥ α^{2B/(δ α^B)} · δ'(B, δ)`. -/
theorem claim_5_14 (Sig : Type) [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ) (hμ : IsDist μ)
    (hmarg : ∀ i : Fin 3, marginal μ i = ν) (hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (hemb : ¬ DistHasEmbedding ℤ μ) (α : ℝ) (hα : IsMinAtom μ α)
    (n B : ℕ) (δ' : ℕ → ℝ → ℝ)
    (hyp : ∀ g : (Fin n → Sig) → ℝ, (∀ x, g x = 0 ∨ g x = 1) → Resilient ν B (1 / 2) g →
      δ' B (expect (tensorPow ν n) g) ≤ Delta1 μ g)
    (f : (Fin n → Sig) → ℝ) (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hδ : 0 < expect (tensorPow ν n) f) :
    α ^ (2 * (B : ℝ) / (expect (tensorPow ν n) f * α ^ B)) *
        δ' B (expect (tensorPow ν n) f) ≤ Delta1 μ f := by sorry

end RestrictedAP.Counting
