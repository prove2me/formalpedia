-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_7
-- name    : RestrictedAP.Counting.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:35.091218+00:00
-- url     : https://prove2.me/theorems/313c02e4-a94e-4d30-9aaf-d16d1e88e26e
-- title:
--   Lemma 3.7 — with high rank and softrank every value pattern is hit by $(x,y,z)\sim\mu$, even after fixing $D/2$ coordinates
-- statement:
--   For all $M,r$ and $\alpha>0$ there is $c=c(M,r,\alpha)>0$ such that the following holds. Let $\mu$ be a distribution on $\Sigma^3$ with $(x,x,x)\in\mathrm{supp}(\mu)$ for every $x\in\Sigma$ and every atom of probability at least $\alpha$; let $\mathcal P$ be a collection of $r$ $M$-discrete (normalized) product functions on $\Sigma^n$ with $\mathrm{rk}(\mathcal P)\ge D$ and $\mathrm{softrk}_\mu(\mathcal P)\ge D$; let $J\subseteq[n]$ with $|J|\le D/2$. Then for every $(w,w',w'')\in\mathrm{supp}(\mu|_J)$ and every $\vec b\in\prod_{P\in\mathcal P}\mathrm{Image}(P)$,
--   $$\Pr_{(x,y,z)\sim\mu_{\bar J}}\big[\forall P\in\mathcal P,\ P(w,x)=P(w',y)=P(w'',z)=b_P\big]\ \ge\ \prod_{P\in\mathcal P}\frac1{\mathrm{ord}(P)^3}-2^{-cD},$$
--   where $P(w,x)$ is $P$ evaluated at the point equal to $w$ on $J$ and to $x$ on $\bar J$. With $J=\emptyset$ this contains Lemma 3.6.
--
--   Differences from the source:
--   - reading: 2^{−Ω_{M,r,α}(D)} → ∃ c > 0 depending only on (M, r, α), quantified before Σ, μ, n, 𝒫, D, J; bound 2^{−c·D}; reason: §2 notation
--   - reading: 'the probability of each atom is at least α' with an Ω_α constant → 0 < α; reason: α is a lower bound on atom probabilities and the constant is a function of α; for α ≤ 0 the hypothesis is void and the bound fails for a point mass
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - encoding: Σ an alphabet of size m → any finite alphabet Σ (m not named); reason: the constant does not depend on m
--   - encoding: w, w′, w″ ∈ Σ^J, x, y, z ∈ Σ^{J̄}, P(w, x), probability over μ_{J̄} → full vectors in Σ^n; P(w, x) is P at the vector equal to w on J and x off J; the probability is over μ^{⊗n} of an event that ignores the coordinates in J; reason: the marginal of μ^{⊗n} on J̄ is μ_{J̄}; same value
--   - encoding: (w, w′, w″) ∈ supp(μ|_J) → μ(w_j, w′_j, w″_j) ≠ 0 for every j ∈ J; reason: the support of a product distribution is the product of the supports
--   - encoding: b⃗ ∈ ∏_{P∈𝒫} Image(P) → b : functions → ℂ with b P ∈ range P for every P ∈ 𝒫; reason: a vector indexed by 𝒫
--   - encoding: ord(P) ∈ ℕ ∪ {∞} → `orderOf P` in the monoid of functions (0 encodes ∞); M-discrete = 0 < orderOf P ≤ M; reason: Mathlib's order of an element is the least k ≥ 1 with P^k = 1, as Definition 2.3
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 18, Lemma 3.7

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

open Classical

namespace RestrictedAP.Counting

/-- **Lemma 3.7** (p. 18). For all `M`, `r` and `α > 0` there is `c = c(M, r, α) > 0` such that:
let `μ` be a distribution on `Σ^3` with `(x, x, x) ∈ supp(μ)` for every `x ∈ Σ` and all atoms of
probability at least `α`, `𝒫` a collection of `r` `M`-discrete `n`-variate (normalized) product
functions with `rk(𝒫) ≥ D` and `softrk_μ(𝒫) ≥ D`, and `J ⊆ [n]` with `|J| ≤ D/2`. Then for every
`(w, w', w'') ∈ supp(μ|_J)` and every `b⃗ ∈ ∏_{P ∈ 𝒫} Image(P)`,
`Pr_{(x,y,z) ∼ μ_{J̄}} [∀ P ∈ 𝒫, P(w, x) = P(w', y) = P(w'', z) = b_P] ≥ ∏_P 1/ord(P)^3 − 2^{−c D}`.

Encoding: `w, w', w''` and `x, y, z` are full vectors in `Σ^n`; `P(w, x)` is `P` evaluated at
the vector equal to `w` on `J` and to `x` off `J`, and the probability over `μ_{J̄}` is written
as the probability over `(x, y, z) ∼ μ^{⊗n}` of an event that ignores the coordinates in `J`. -/
theorem lemma_3_7 (M r : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (μ : Sig × Sig × Sig → ℝ)
        (n : ℕ) (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ) (J : Finset (Fin n)),
        IsDist μ → (∀ x : Sig, μ (x, x, x) ≠ 0) → AtomsAtLeast μ α → PP.card = r →
        (∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P) →
        RankAtLeast PP (D : ℝ) → SoftRankMuAtLeast μ PP (D : ℝ) →
        (J.card : ℝ) ≤ (D : ℝ) / 2 →
        ∀ w w' w'' : Fin n → Sig, (∀ j ∈ J, μ (w j, w' j, w'' j) ≠ 0) →
        ∀ b : ((Fin n → Sig) → ℂ) → ℂ, (∀ P ∈ PP, b P ∈ Set.range P) →
          (∏ P ∈ PP, (1 / (orderOf P : ℝ) ^ 3)) - (2 : ℝ) ^ (-(c * D)) ≤
            ∑ t : Fin n → Sig × Sig × Sig,
              if (∀ P ∈ PP,
                  P (fun i => if i ∈ J then w i else (t i).1) = b P ∧
                  P (fun i => if i ∈ J then w' i else (t i).2.1) = b P ∧
                  P (fun i => if i ∈ J then w'' i else (t i).2.2) = b P)
              then tensorPow μ n t else 0 := by sorry

end RestrictedAP.Counting
