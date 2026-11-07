-- Prove2me | Theorems.Thm_UltrametricFit_claim_10
-- name    : UltrametricFit.claim_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:15.058168+00:00
-- url     : https://prove2.me/theorems/7b336dc6-fbf7-4f11-8afe-9a2a3c57a4cb
-- title:
--   Claim 10, p.9 — the interpolation of two children has small expected distance
-- statement:
--   Let $d$ be a pseudometric, $\delta\ge0$, and let $A$ be a non-leaf node of a $\delta$-merge forest with children $A_1,A_2$. For each $t\in[0,1]$, if $i,j$ are independent draws from the interpolation $\mu_t(A)$, then
--   $$\mathbb E_{i,j\sim\mu_t(A)}[d(i,j)]\le\delta.$$
--   This extends Claim 8 from the uniform law on $A$ to every mixture of the uniform laws on the two children.
--
--   Differences from the source:
--   - generalization: a metric $d$ → a pseudometric (zero distances between distinct species are allowed); reason: every metric is a pseudometric, and the paper applies the result to the LP layers $x_\ell$, which it calls technically a pseudometric (p.2)
--   - encoding: $\delta$-merge forest for a $\delta$ left unspecified in §4.1 → $0\le\delta$; reason: the paper's $\delta$ lies in $(0,0.5)$ (§3); the bound fails for a singleton when $\delta<0$, so this excludes no instance of the paper
--   - encoding: $\mathbb E_{i,j\sim\mu_t(A)}$ of a distribution → the double sum over $A_1\cup A_2$ with product point masses; reason: independent draws, as the page's expansion shows; a finite expectation
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Claim 10, p.9

import Mathlib
import Definitions.Def_UltrametricFit_IsMergeNode

namespace UltrametricFit

/-- **Claim 10**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.9: for each
non-leaf node `A` with children `A₁, A₂` and each `t ∈ [0, 1]`, `E_{i,j∼μ_t(A)}[d(i, j)] ≤ δ`.

**Formalization Note.** `i, j` are independent draws from `μ_t(A)`, as the page's expansion shows,
so the expectation is the double sum with product weights. The hypotheses on `A₁, A₂` are those of
the `union` constructor of `IsMergeNode`. -/
theorem claim_10 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsPseudometric d) (δ : ℝ) (hδ : 0 ≤ δ)
    (A₁ A₂ : Finset (Fin n)) (h₁ : IsMergeNode d δ A₁) (h₂ : IsMergeNode d δ A₂)
    (hdisj : Disjoint A₁ A₂) (hle : avgDist d A₁ A₂ ≤ δ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i ∈ A₁ ∪ A₂, ∑ j ∈ A₁ ∪ A₂, interpWeight A₁ A₂ t i * interpWeight A₁ A₂ t j * d i j ≤ δ := by sorry

end UltrametricFit
