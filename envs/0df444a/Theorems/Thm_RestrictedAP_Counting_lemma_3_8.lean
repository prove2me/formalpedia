-- Prove2me | Theorems.Thm_RestrictedAP_Counting_lemma_3_8
-- name    : RestrictedAP.Counting.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:20:49.541501+00:00
-- url     : https://prove2.me/theorems/28245d99-ab16-4009-9c7a-12da1819e446
-- title:
--   Lemma 3.8 — with high softrank the noisy indicator of a value-pattern set is close to its mean
-- statement:
--   For all $M,r$, $\alpha>0$ and $\kappa\in(0,1]$ there is $c=c(\alpha,\kappa,r,M)>0$ such that the following holds. Let $\mu$ be a distribution on $\Sigma^3$ with $(x,x,x)\in\mathrm{supp}(\mu)$ for every $x$ and every atom of probability at least $\alpha$; let $\mathcal P$ be a collection of $r$ $M$-discrete (normalized) product functions on $\Sigma^n$ with $\mathrm{softrk}_\mu(\mathcal P)\ge D$, and $J\subseteq[n]$ with $|J|\le D/2$. For $(w,w',w'')\in\mathrm{supp}(\mu|_J)$ and $\vec a,\vec b,\vec c\in\prod_{P}\mathrm{Image}(P)$ let $S_{\vec a}=\{x\in\Sigma^{\bar J}:P(w,x)=a_P\ \forall P\}$, $S_{\vec b}=\{y:P(w',y)=b_P\ \forall P\}$, $S_{\vec c}=\{z:P(w'',z)=c_P\ \forall P\}$ and $S=S_{\vec a}\times S_{\vec b}\times S_{\vec c}\subseteq(\Sigma^{\bar J})^3$. Then
--   $$\big\|T_{1-\kappa}1_S-\mu(S)\big\|_{L^2(\mu)}\le2^{-cD},$$
--   where $T_{1-\kappa}=T_{1-\kappa,\mu}$ keeps each coordinate triple with probability $1-\kappa$ and resamples it from $\mu$ otherwise, and $\mu(S)$ is the $\mu^{\otimes\bar J}$-probability of $S$.
--
--   Differences from the source:
--   - reading: 2^{−Ω_{α,κ,r,M}(D)} → ∃ c > 0 depending only on (α, κ, r, M), quantified before Σ, μ, n, 𝒫, D, J; bound 2^{−c·D}; reason: §2 notation
--   - reading: κ unrestricted in the statement → κ ∈ (0, 1]; reason: T_{1−κ} is defined (p. 20, Definition 2.6) only for 1 − κ ∈ [0, 1]; at κ = 0 the operator is the identity and no decay in D is possible
--   - reading: 'the probability of each atom is at least α' with an Ω_α constant → 0 < α; reason: α is a lower bound on atom probabilities and the constant is a function of α; for α ≤ 0 the hypothesis is void and the bound fails for a point mass
--   - reading: product functions (the theorem's sentence) → product functions normalized at a distinguished σ⋆: factors of modulus 1 with P_i(σ⋆) = 1 (`IsProductFunction σs`); reason: §2.1 (p. 7): 'Unless specified otherwise, throughout this paper we will consider normalized product functions'
--   - encoding: Σ an alphabet of size m → any finite alphabet Σ (m not named); reason: the constant does not depend on m
--   - encoding: S ⊆ (Σ^{J̄})^3, T_{1−κ} on (Σ^{J̄})^3, L²(μ_{J̄}) → the indicator of S lifted to (Σ^3)^n (ignoring the coordinates in J), `noiseOp μ (1 − κ) n` on the alphabet Σ×Σ×Σ and the norm of L²(μ^{⊗n}); reason: on functions of the coordinates outside J the product operator and the norm agree with those on (Σ^{J̄})^3
--   - encoding: (w, w′, w″) ∈ supp(μ|_J) → μ(w_j, w′_j, w″_j) ≠ 0 for every j ∈ J; reason: the support of a product distribution is the product of the supports
--   - encoding: b⃗ ∈ ∏_{P∈𝒫} Image(P) → b : functions → ℂ with b P ∈ range P for every P ∈ 𝒫; reason: a vector indexed by 𝒫
--   - encoding: a collection 𝒫 of product functions and |𝒫| → a `Finset` of functions `(Fin n → Σ) → ℂ` and its card; reason: a collection is a set of functions
--   - encoding: distributions over finite alphabets, ν^{⊗n}, Pr and E → nonnegative weight functions summing to 1 (`IsDist`), product weights (`tensorPow`), finite sums; reason: finite probability spaces; same instances
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), pp. 20–21, Lemma 3.8

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators

open Classical

namespace RestrictedAP.Counting

/-- **Lemma 3.8** (pp. 20–21). For all `M`, `r`, `α > 0` and `κ ∈ (0, 1]` there is
`c = c(α, κ, r, M) > 0` such that: let `μ` be a distribution on `Σ^3` with `(x, x, x) ∈ supp(μ)`
for every `x ∈ Σ` and all atoms of probability at least `α`, `𝒫` a collection of `r` `M`-discrete
`n`-variate (normalized) product functions with `softrk_μ(𝒫) ≥ D`, and `J ⊆ [n]` with
`|J| ≤ D/2`. Then for every `(w, w', w'') ∈ supp(μ|_J)` and `a⃗, b⃗, c⃗ ∈ ∏_{P ∈ 𝒫} Image(P)`, with
`S = S_a⃗ × S_b⃗ × S_c⃗`, `S_a⃗ = {x ∈ Σ^{J̄} : P(w, x) = a_P ∀ P}` (and likewise `S_b⃗` with `w'`,
`S_c⃗` with `w''`), `‖T_{1−κ} 1_S − μ(S)‖_{L²(μ)} ≤ 2^{−c D}`, where `T_{1−κ}` is the noise
operator `T_{1−κ,μ}` on `(Σ^{J̄})^3`.

Encoding: as in Lemma 3.7, `S` is lifted to `(Σ^3)^n` (a sample `t` gives `x = (t i).1`,
`y = (t i).2.1`, `z = (t i).2.2`) by an indicator that ignores the coordinates in `J`; the noise
operator is `noiseOp μ (1 − κ) n` on the alphabet `Σ × Σ × Σ` and the norm is that of
`L²(μ^{⊗n})`. On functions of the coordinates outside `J` these agree with the operator and the
norm on `(Σ^{J̄})^3`. -/
theorem lemma_3_8 (M r : ℕ) (α κ : ℝ) (hα : 0 < α) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (μ : Sig × Sig × Sig → ℝ)
        (n : ℕ) (PP : Finset ((Fin n → Sig) → ℂ)) (D : ℤ) (J : Finset (Fin n)),
        IsDist μ → (∀ x : Sig, μ (x, x, x) ≠ 0) → AtomsAtLeast μ α → PP.card = r →
        (∀ P ∈ PP, IsProductFunction σs P ∧ IsDiscrete M P) →
        SoftRankMuAtLeast μ PP (D : ℝ) →
        (J.card : ℝ) ≤ (D : ℝ) / 2 →
        ∀ w w' w'' : Fin n → Sig, (∀ j ∈ J, μ (w j, w' j, w'' j) ≠ 0) →
        ∀ a b c' : ((Fin n → Sig) → ℂ) → ℂ,
          (∀ P ∈ PP, a P ∈ Set.range P) → (∀ P ∈ PP, b P ∈ Set.range P) →
          (∀ P ∈ PP, c' P ∈ Set.range P) →
          let inS : (Fin n → Sig × Sig × Sig) → Prop := fun t =>
            (∀ P ∈ PP, P (fun i => if i ∈ J then w i else (t i).1) = a P) ∧
            (∀ P ∈ PP, P (fun i => if i ∈ J then w' i else (t i).2.1) = b P) ∧
            (∀ P ∈ PP, P (fun i => if i ∈ J then w'' i else (t i).2.2) = c' P)
          let oneS : (Fin n → Sig × Sig × Sig) → ℂ := fun t => if inS t then 1 else 0
          let μS : ℝ := ∑ t : Fin n → Sig × Sig × Sig, if inS t then tensorPow μ n t else 0
          l2Norm (tensorPow μ n) (fun t => noiseOp μ (1 - κ) n oneS t - (μS : ℂ)) ≤
            (2 : ℝ) ^ (-(c * D)) := by sorry

end RestrictedAP.Counting
