-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_5
-- name    : RestrictedAP.Counting.lemma_3_5
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:35.775633+00:00
-- url     : https://prove2.me/theorems/fe3fa1c8-785c-421b-9389-85f4474bb239
-- title:
--   Lemma 3.5 — the values of a high-rank collection are nearly uniformly distributed
-- statement:
--   For all $M,r$ and $\alpha>0$ there is $c=c(M,r,\alpha)>0$ such that: if $\nu$ is a distribution on a finite alphabet $\Sigma$ in which every atom has probability at least $\alpha$, and $\mathcal P$ is a collection of $r$ $M$-discrete (normalized) product functions on $\Sigma^n$ with $\mathrm{rk}(\mathcal P)\ge D$, then for every $\vec b\in\prod_{P\in\mathcal P}\mathrm{Image}(P)$
--   $$\Big|\Pr_{x\sim\nu^{\otimes n}}\big[\forall P\in\mathcal P,\ P(x)=b_P\big]-\prod_{P\in\mathcal P}\frac1{\mathrm{ord}(P)}\Big|\le2^{-cD}.$$
--
--   Differences from the source:
--   - reading: 2^{−Ω_{M,r,α}(D)} → ∃ c > 0 depending only on (M, r, α), quantified before Σ, ν, n, 𝒫, D; bound 2^{−c·D}; reason: §2 notation
--   - reading: 'the probability of each atom is at least α' with an Ω_α constant → 0 < α; reason: α is a lower bound on atom probabilities and the constant is a function of α; for α ≤ 0 the hypothesis is void and the bound fails for a point mass
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - encoding: Σ an alphabet of size m → any finite alphabet Σ (m not named); reason: the constant does not depend on m, so the statement for every m is the statement for every finite Σ
--   - encoding: b⃗ ∈ ∏_{P∈𝒫} Image(P) → b : functions → ℂ with b P ∈ range P for every P ∈ 𝒫; reason: a vector indexed by 𝒫
--   - encoding: ord(P) ∈ ℕ ∪ {∞} → `orderOf P` in the monoid of functions (0 encodes ∞); M-discrete = 0 < orderOf P ≤ M; reason: Mathlib's order of an element is the least k ≥ 1 with P^k = 1, as Definition 2.3
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 17, Lemma 3.5

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions

open Classical

namespace RestrictedAP.Counting

/-- **Lemma 3.5** (p. 17). For all `M`, `r` and `α > 0` there is `c = c(M, r, α) > 0` such that:
if `ν` is a distribution on an alphabet `Σ` all of whose atoms have probability at least `α`,
`𝒫` is a collection of `r` `M`-discrete `n`-variate (normalized) product functions with
`rk(𝒫) ≥ D`, then for every `b⃗ ∈ ∏_{P ∈ 𝒫} Image(P)`,
`|Pr_{x ∼ ν^{⊗n}}[∀ P ∈ 𝒫, P(x) = b_P] − ∏_{P ∈ 𝒫} 1/ord(P)| ≤ 2^{−c D}`. -/
theorem lemma_3_5 (M r : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ),
        IsDist ν → AtomsAtLeast ν α → PP.card = r →
        (∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P) →
        RankAtLeast PP (D : ℝ) →
        ∀ b : ((Fin n → Sig) → ℂ) → ℂ, (∀ P ∈ PP, b P ∈ Set.range P) →
          |(∑ x : Fin n → Sig, if (∀ P ∈ PP, P x = b P) then tensorPow ν n x else 0) -
              ∏ P ∈ PP, (1 / (orderOf P : ℝ))| ≤ (2 : ℝ) ^ (-(c * D)) := by sorry

end RestrictedAP.Counting
