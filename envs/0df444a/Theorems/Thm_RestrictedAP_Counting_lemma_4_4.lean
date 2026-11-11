-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_4_4
-- name    : RestrictedAP.Counting.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:57.069201+00:00
-- url     : https://prove2.me/theorems/d16c8482-02b6-418f-a1b1-8966163a08b4
-- title:
--   Lemma 4.4 — arithmetic regularity lemma with high rank and high softrank
-- statement:
--   For every $m$ there is $M=M(m)$ and, for every $\alpha>0$, a threshold decay function $w_0$ such that for every decay function $w\le w_0$ ("sufficiently rapid") and every $\xi>0$ there is $c=c(w,m,\alpha,\xi)>0$ with the following property. Let $\Sigma$ be a finite alphabet with $|\Sigma|\le m$, $\nu$ a distribution on $\Sigma$ with every atom of probability at least $\alpha$, $\mu$ a distribution on $\Sigma^3$ with all three marginals equal to $\nu$, and $f:\Sigma^n\to\mathbb C$ $1$-bounded. Then there are $w$-separated scales $\rho_5\ll_w\rho_4\ll_w\rho_3\ll_w\rho_2\ll_w\rho_1\ll_w\rho_0$ in $(0,1)$ (that is, $\rho_{j+1}\le w(\rho_j)$) with $\rho_0\le\xi$ and $\rho_5\ge c$, and collections $\mathcal P,\mathcal P'$ of cyclic (normalized) product functions such that
--
--   1. (a) $|\mathcal P|\le1/\rho_0$; (b) $\mathcal P$ is $M$-discrete; (c) $\|f-T_{\mathcal P,1-\rho_1}f\|_\nu\le\xi$; (d) $\mathrm{rk}(\mathcal P)\ge1/\rho_2$; (e) $\mathrm{softrk}_\mu(\mathcal P)\ge1/\rho_2$;
--   2. $|\mathcal P'|\le1/\rho_4$, $\mathcal P'$ is $M$-discrete, and $\|f-T_{\mathcal P',1-\rho_5}f\|_\nu\le\rho_3$;
--   3. $\|T_{\mathcal P',1-\rho_5}f-T_{\mathcal P,1-\rho_1}f\|_2\le\xi$.
--
--   This is the paper's main new ingredient: a regularity decomposition whose structured part comes from a collection that is simultaneously of high rank and high softrank.
--
--   Differences from the source:
--   - reading: w a sufficiently rapid decay function → ∃ a decay function w₀ (depending on m, α) such that the conclusion holds for every decay function w with w ≤ w₀ on (0,1); reason: the usual meaning of 'sufficiently rapid'; w₀ is itself a decay function, so the class of admissible w is nonempty
--   - reading: O_m(1)-discrete → ∃ M = M(m), quantified before α, w, ξ, Σ, ν, μ, f, and both collections are M-discrete; reason: §2 notation
--   - reading: ρ₅ ≥ Ω_{w,m,α,ξ}(1) → ∃ c > 0 chosen after w and ξ, before Σ, ν, μ, n, f, with c ≤ ρ₅; reason: §2 notation: the constant depends only on the subscripts
--   - encoding: w-separated scales ρ₅ ≪_w … ≪_w ρ₀ → six reals in (0,1) with ρ_{j+1} ≤ w(ρ_j); reason: the scales are arguments of w : (0,1) → (0,1) (p. 7 definition)
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - reading: ∥·∥_ν, M_ν with 'pairwise connected' (not defined in the paper) → `nuNorm ν α` with the α of the atom bound (Definition 2.19); pairwise connected = for each pair of coordinates the bipartite graph of pairs occurring in an atom of μ is connected on its non-isolated vertices; reason: Definition 2.19 'when α is clear from context we write ∥f∥_ν'; the [BKM24b] notion
--   - encoding: decay function w : (0,1) → (0,1), monotonically increasing with w(ε) ≤ ε → w : ℝ → ℝ with these properties required on (0,1) (`IsDecay`); reason: values outside (0,1) are never used
--   - encoding: ord(P) ∈ ℕ ∪ {∞} → `orderOf P` in the monoid of functions (0 encodes ∞); M-discrete = 0 < orderOf P ≤ M; reason: Mathlib's order of an element is the least k ≥ 1 with P^k = 1, as Definition 2.3
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), pp. 26–27, Lemma 4.4

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators
import Definitions.Def_RestrictedAP_Counting_Seminorms

namespace RestrictedAP.Counting

/-- **Lemma 4.4** (pp. 26–27), the arithmetic regularity lemma with high rank and softrank.
For every `m` there is `M = O_m(1)`, and for every `α > 0` a threshold decay function `w₀`
("sufficiently rapid"), such that for every decay function `w : (0,1) → (0,1)` with `w ≤ w₀`
and every `ξ > 0` there is `c = c(w, m, α, ξ) > 0` with the following property. For every finite
alphabet `Σ` with `|Σ| ≤ m`, distribution `ν` on `Σ` with all atoms of probability at least
`α`, distribution `μ` on `Σ^3` with all three marginals equal to `ν`, and `1`-bounded
`f : Σ^n → ℂ`, there are `w`-separated scales `ρ₅ ≪_w ρ₄ ≪_w ρ₃ ≪_w ρ₂ ≪_w ρ₁ ≪_w ρ₀` in `(0,1)`
(`ρ_{j+1} ≤ w(ρ_j)`) with `ρ₀ ≤ ξ` and `ρ₅ ≥ c`, and collections `𝒫, 𝒫'` of cyclic (normalized)
product functions with
1. (a) `|𝒫| ≤ 1/ρ₀`, (b) `𝒫` is `M`-discrete, (c) `‖f − T_{𝒫,1−ρ₁} f‖_ν ≤ ξ`,
   (d) `rk(𝒫) ≥ 1/ρ₂`, (e) `softrk_μ(𝒫) ≥ 1/ρ₂`;
2. `|𝒫'| ≤ 1/ρ₄`, `𝒫'` is `M`-discrete, and `‖f − T_{𝒫',1−ρ₅} f‖_ν ≤ ρ₃`;
3. `‖T_{𝒫',1−ρ₅} f − T_{𝒫,1−ρ₁} f‖₂ ≤ ξ`.
Here `‖·‖_ν = ‖·‖_{ν,α}` and `‖·‖₂` is the norm of `L²(ν^{⊗n})`. -/
theorem lemma_4_4 (m : ℕ) :
    ∃ M : ℕ, ∀ α : ℝ, 0 < α →
    ∃ w₀ : ℝ → ℝ, IsDecay w₀ ∧
    ∀ w : ℝ → ℝ, IsDecay w → (∀ ε, 0 < ε → ε < 1 → w ε ≤ w₀ ε) →
    ∀ ξ : ℝ, 0 < ξ → ∃ c : ℝ, 0 < c ∧
    ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ)
      (μ : Sig × Sig × Sig → ℝ),
      Fintype.card Sig ≤ m → IsDist ν → AtomsAtLeast ν α → IsDist μ →
      (∀ i : Fin 3, marginal μ i = ν) →
    ∀ (n : ℕ) (f : (Fin n → Sig) → ℂ), (∀ x, ‖f x‖ ≤ 1) →
    ∃ ρ₀ ρ₁ ρ₂ ρ₃ ρ₄ ρ₅ : ℝ,
      (0 < ρ₀ ∧ ρ₀ < 1) ∧ (0 < ρ₁ ∧ ρ₁ < 1) ∧ (0 < ρ₂ ∧ ρ₂ < 1) ∧
      (0 < ρ₃ ∧ ρ₃ < 1) ∧ (0 < ρ₄ ∧ ρ₄ < 1) ∧ (0 < ρ₅ ∧ ρ₅ < 1) ∧
      ρ₁ ≤ w ρ₀ ∧ ρ₂ ≤ w ρ₁ ∧ ρ₃ ≤ w ρ₂ ∧ ρ₄ ≤ w ρ₃ ∧ ρ₅ ≤ w ρ₄ ∧
      ρ₀ ≤ ξ ∧ c ≤ ρ₅ ∧
    ∃ PP PP' : Finset ((Fin n → Sig) → ℂ),
      (∀ P ∈ PP, IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
      (∀ P ∈ PP', IsProductFunction σs P ∧ IsCyclic P ∧ IsDiscrete M P) ∧
      -- item 1 (a), (c), (d), (e); (b) is in the line above
      (PP.card : ℝ) ≤ 1 / ρ₀ ∧
      nuNorm ν α (f - condNoise ν PP ρ₁ f) ≤ ξ ∧
      RankAtLeast PP (1 / ρ₂) ∧
      SoftRankMuAtLeast μ PP (1 / ρ₂) ∧
      -- item 2
      (PP'.card : ℝ) ≤ 1 / ρ₄ ∧
      nuNorm ν α (f - condNoise ν PP' ρ₅ f) ≤ ρ₃ ∧
      -- item 3
      l2Norm (tensorPow ν n) (condNoise ν PP' ρ₅ f - condNoise ν PP ρ₁ f) ≤ ξ := by sorry

end RestrictedAP.Counting
