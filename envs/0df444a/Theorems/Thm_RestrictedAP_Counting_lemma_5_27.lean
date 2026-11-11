-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_5_27
-- name    : RestrictedAP.Counting.lemma_5_27
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:50.23219+00:00
-- url     : https://prove2.me/theorems/1fc1c3fb-cd1b-4a65-b096-e3bc9a7842cc
-- title:
--   Lemma 5.27 — counting lemma for resilient functions
-- statement:
--   Setting of §5.2. For all $m$, $\alpha>0$ and $\delta>0$ there are $B_0\in\mathbb N$ and $c>0$ such that the following holds. Let $\Sigma$ be a finite alphabet with $|\Sigma|\le m$ and $\mu$ a distribution on $\Sigma^3$ all of whose marginals equal $\nu$, with $(x,x,x)\in\mathrm{supp}(\mu)$ for every $x$, no $(\mathbb Z,+)$-embedding, and minimum non-zero atom probability $\alpha$. Then for every $n$, every $B\ge B_0$ and every $(B,1/2)$-resilient $f:\Sigma^n\to\{0,1\}$ with $\nu^{\otimes n}(f)\ge\delta$,
--   $$\Delta_1(f)\ \ge\ \alpha^{B+1}\cdot c .$$
--
--   The printed statement reads "$B\gg\Omega_{\rho_1}(1)$, then $\Delta_1(f)\ge\alpha^{B+1}\Omega_{\rho_0}(\delta^{\Omega_{m,\alpha}(1)})$", where $\rho_0,\rho_1$ are the scales Lemma 4.4 produces for $f$ with $\xi$ chosen in terms of $\delta,\alpha,m$ and $\delta$ is the density of §5.2; since those scales are bounded below in terms of $(m,\alpha,\delta)$ (Lemma 4.4's $\rho_5\ge\Omega_{w,m,\alpha,\xi}(1)$), both the threshold for $B$ and the factor multiplying $\alpha^{B+1}$ are constants depending only on $(m,\alpha,\delta)$.
--
--   Differences from the source:
--   - reading: B ≫ Ω_{ρ₁}(1) and the factor Ω_{ρ₀}(δ^{Ω_{m,α}(1)}), with ρ₀, ρ₁ from Lemma 4.4 applied to f → ∃ B₀ ∈ ℕ and c > 0 depending only on (m, α, δ), quantified before Σ, μ, n, B, f; the conclusion holds for every B ≥ B₀ with factor c; reason: ρ₀, ρ₁ are bounded below in terms of (m, α, δ) by Lemma 4.4 with ξ = ξ(δ, α, m); the lemma is not self-contained as printed
--   - reading: δ (the density of §5.2: |A|/|Σ|^n ≥ δ, Claim 5.14: ν^{⊗n}(f) = δ) → a parameter δ > 0 with δ ≤ ν^{⊗n}(f); reason: δ is a density lower bound for f
--   - reading: the claim's sentence (Σ, μ, ν, α fixed by §5.2) → hypotheses: μ a distribution on Σ^3 with all marginals ν, (x, x, x) ∈ supp(μ) for every x, no (ℤ,+)-embedding, α the minimum non-zero atom probability; reason: standing assumptions of §5.2 (p. 31): the setting of Theorem 1.4 with 'the minimum non-zero probability of the distribution µ is α'
--   - encoding: f : Σ^n → {0, 1} → a real-valued function with f(x) ∈ {0, 1} for every x; reason: indicators as real functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 47, Lemma 5.27

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience

namespace RestrictedAP.Counting

/-- **Lemma 5.27** (p. 47), the counting lemma for resilient functions, in the setting of §5.2.
Reading of the printed `B ≫ Ω_{ρ₁}(1)` and `Ω_{ρ₀}(δ^{Ω_{m,α}(1)})`: for all `m`, `α > 0` and
`δ > 0` there are `B₀ ∈ ℕ` and `c > 0` (depending only on `m, α, δ`) such that for every finite
alphabet `Σ` with `|Σ| ≤ m`, every distribution `μ` on `Σ^3` with all marginals equal to `ν`,
`(x, x, x) ∈ supp(μ)` for every `x`, no `(ℤ,+)`-embedding and minimum non-zero atom probability
`α`, every `n`, every `B ≥ B₀`, and every `(B, 1/2)`-resilient `f : Σ^n → {0,1}` with
`ν^{⊗n}(f) ≥ δ`: `Δ₁(f) ≥ α^{B+1} · c`. -/
theorem lemma_5_27 (m : ℕ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig], Fintype.card Sig ≤ m →
      ∀ (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ), IsDist μ →
        (∀ i : Fin 3, marginal μ i = ν) → (∀ x : Sig, μ (x, x, x) ≠ 0) →
        ¬ DistHasEmbedding ℤ μ → IsMinAtom μ α →
      ∀ (n B : ℕ), B₀ ≤ B →
      ∀ f : (Fin n → Sig) → ℝ, (∀ x, f x = 0 ∨ f x = 1) → Resilient ν B (1 / 2) f →
        δ ≤ expect (tensorPow ν n) f →
        α ^ (B + 1) * c ≤ Delta1 μ f := by sorry

end RestrictedAP.Counting
