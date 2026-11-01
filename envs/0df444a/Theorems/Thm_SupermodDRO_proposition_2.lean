-- Prove2me | Theorems.Thm_SupermodDRO_proposition_2
-- name    : SupermodDRO.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:28.756267+00:00
-- url     : https://prove2.me/theorems/83a1062c-cd70-4811-8654-c9ff194751aa
-- title:
--   Proposition 2, p.9 — $f$ is supermodular iff every finite-marginal problem has a chain-supported worst case
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be any function. The following are equivalent.
--
--   1. $f$ is supermodular: $f(w')+f(w'')\le f(w'\wedge w'')+f(w'\vee w'')$ for all $w',w''\in\mathbb R^n$.
--   2. For all integers $m_i\ge1$, points $x_{i1}<\dots<x_{im_i}$ and probabilities $p_{ij}>0$ with $\sum_jp_{ij}=1$ ($i\in[n]$), let $\mathcal P$ be the set of distributions $\mathbb P$ of $\tilde w$ with $\mathbb P(\tilde w_i=x_{ij})=p_{ij}$ for all $i,j$. Then some $\mathbb P^*\in\arg\sup_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}[f(\tilde w)]$ has a support
--   $$
--   \mathcal W_{\mathbb P^*}=\{w\in\mathbb R^n:\mathbb P^*(\tilde w=w)>0\}
--   $$
--   that is a chain (any two of its points are ordered componentwise) with at most $\sum_{i\in[n]}(m_i-1)+1$ points.
--
--   The direction 1 ⇒ 2 is the comonotone structure of the worst case; 2 ⇒ 1 says this structure occurs only for supermodular $f$. No continuity of $f$ is assumed.
--
--   **Formalization Note** Every $\mathbb P\in\mathcal P$ is concentrated on the finite grid $\prod_i\{x_{i1},\dots,x_{im_i}\}$, so it is a nonnegative mass function of total mass $1$ on the index grid with the prescribed marginal sums, and $\mathbb E_{\mathbb P}[f]$ is a finite sum.
--
--   Differences from the source:
--   - encoding: 𝒫 = distributions ℙ on ℜⁿ with ℙ(w̃ᵢ = xᵢⱼ) = pᵢⱼ, and E_ℙ[f(w̃)] → nonnegative mass functions of total mass 1 on the index grid ∏ᵢ[mᵢ] with these marginal sums, and the finite sum; reason: every ℙ ∈ 𝒫 is concentrated on the finite grid, so both descriptions have the same instances
--   - encoding: f is supermodular (Definition 1) → SupermodularOn univ of f viewed in EReal; reason: for real values it is the inequality of Definition 1
--   - encoding: [K], [n], [2n+1] indexed from 1 → Fin K, Fin n, Fin (2n+1) indexed from 0; reason: Lean convention; same instances
-- source:
--   Long, Qi & Zhang, Supermodularity in Two-Stage Distributionally Robust Optimization, author manuscript (June 2022; PDF sha256 9e6840ad…5b09160b02b5e47), Proposition 2, p.9

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Supermodular

namespace SupermodDRO

/-- **Proposition 2 (supermodularity ⇔ chain-supported worst cases for finite marginals).**
Long, Qi & Zhang, *Supermodularity in Two-Stage Distributionally Robust Optimization*, author
manuscript (June 2022), Proposition 2, p.9: "Consider any function f : ℜⁿ → ℜ. The following
statements are equivalent. 1) f is supermodular. 2) Consider any given strictly positive integers mᵢ
and p_{ij} > 0, x_{ij}, j ∈ [mᵢ] such that x_{i1} < ⋯ < x_{imᵢ} and Σ_{j∈[mᵢ]} p_{ij} = 1, for all
i ∈ [n]. Define 𝒫 = {ℙ | ℙ(w̃ᵢ = x_{ij}) = p_{ij}, j ∈ [mᵢ], i ∈ [n]}. Then there exists
ℙ* ∈ arg sup_{ℙ∈𝒫} E_ℙ[f(w̃)] such that the set 𝒲_{ℙ*} = {w ∈ ℜⁿ | ℙ*(w̃ = w) > 0} forms a chain of
at most (Σ_{i∈[n]}(mᵢ − 1) + 1) points."

Supermodularity is Definition 1 (p.8): `f(w′) + f(w″) ≤ f(w′ ∧ w″) + f(w′ ∨ w″)` for all `w′, w″`.

**Formalization Note** Every `ℙ ∈ 𝒫` is concentrated on the finite grid `∏ᵢ {x_{i1}, …, x_{imᵢ}}`
(each marginal has total mass `1` on its `mᵢ` points), so `ℙ` is a nonnegative mass function `π` on
the index grid `w : (i : [n]) → [mᵢ]` with total mass `1`, the point of index `w` being
`(x_{i,wᵢ})ᵢ`; the constraint `ℙ(w̃ᵢ = x_{ij}) = p_{ij}` is a marginal sum and `E_ℙ[f(w̃)]` is a
finite sum. (The total-mass condition follows from the marginal sums when `n ≥ 1` and keeps `ℙ` a
probability measure when `n = 0`.) Being in the arg sup
is `π ∈ 𝒫` and `E_π[f] ≥ E_{π′}[f]` for every `π′ ∈ 𝒫`. A chain is a set of pairwise ordered points
(componentwise order). Supermodularity of the real `f` is the published
`MDPFinance.StructuredModels.SupermodularOn` on the whole space applied to `f` viewed in `EReal`,
which for real values is the inequality of Definition 1. Indices are 0-based. -/
theorem proposition_2 {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    MDPFinance.StructuredModels.SupermodularOn Set.univ (fun w => (f w : EReal)) ↔
      ∀ (m : Fin n → ℕ) (xs : (i : Fin n) → Fin (m i) → ℝ) (p : (i : Fin n) → Fin (m i) → ℝ),
        (∀ i, 0 < m i) → (∀ i, StrictMono (xs i)) → (∀ i j, 0 < p i j) →
        (∀ i, ∑ j, p i j = 1) →
        ∃ π : ((i : Fin n) → Fin (m i)) → ℝ,
          (∀ w, 0 ≤ π w) ∧ ∑ w, π w = 1 ∧
          (∀ i j, ∑ w ∈ Finset.univ.filter (fun w => w i = j), π w = p i j) ∧
          (∀ π' : ((i : Fin n) → Fin (m i)) → ℝ, (∀ w, 0 ≤ π' w) → ∑ w, π' w = 1 →
            (∀ i j, ∑ w ∈ Finset.univ.filter (fun w => w i = j), π' w = p i j) →
            ∑ w, π' w * f (fun i => xs i (w i)) ≤ ∑ w, π w * f (fun i => xs i (w i))) ∧
          (∀ w w', 0 < π w → 0 < π w' →
            ((fun i => xs i (w i)) ≤ (fun i => xs i (w' i)) ∨
              (fun i => xs i (w' i)) ≤ (fun i => xs i (w i)))) ∧
          ((Finset.univ.filter (fun w => 0 < π w)).image
              (fun w => (fun i => xs i (w i) : Fin n → ℝ))).card ≤ ∑ i, (m i - 1) + 1 := by sorry

end SupermodDRO
