-- Prove2me | Theorems.Thm_TwoStageMatch_Supplement_lemma_3
-- name    : TwoStageMatch.Supplement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:12:09.901895+00:00
-- url     : https://prove2.me/theorems/d2c4ea5c-9cc9-4a10-865e-906d95e1aeb5
-- title:
--   Lemma 3: $c^{(l)}=(|S^{(l)}|-|D^{(l)}|)/\sum_{j\in S^{(l)}}1/w_j$ on every component level
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be differentiable, monotone increasing and strictly convex, let all supply weights be positive, and let $x^*$ be an optimal solution of the balancing program $\mathcal P^g$. Consider the structural decomposition of Lemma 1: $S^{(0)}$ are the supplies with load $y_j^*=\sum_ix^*_{ij}=1$, $D^{(0)}$ the first-stage demands with positive mass on $S^{(0)}$, and the levels $l\ge1$ are the connected components of the support graph of $x^*$ on the remaining vertices, with slacks $c^{(l)}=w_j(1-y_j^*)$ for $j\in S^{(l)}$. For every component level $l$ containing a supply vertex,
--   $$c^{(l)}=\frac{|S^{(l)}|-|D^{(l)}|}{\sum_{j\in S^{(l)}}1/w_j}.$$
--
--   The formula pins the slack of a component to its sizes and weights; the factor-revealing programs of Proposition 4 and Theorem EC.2 rest on it.
--
--   **Formalization Note** Levels, slacks and the level maps are those of the published decomposition module.
--
--   Differences from the source:
--   - encoding: every level l ∈ [1 : L] of the decomposition → every component level containing a supply vertex; reason: on a component without supply (the case the published Lemma 1 corrects) the formula is (0 − 1)/0 and undefined
--   - encoding: weights w_j ≥ 0 (p.9) → w_j > 0 for every j; reason: the formula and the program 𝒫^g divide by w_j, so they are undefined when some w_j = 0
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Lemma 3, p.20

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_Decomposition

namespace TwoStageMatch.Supplement

open Classical in
/-- **Lemma 3** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.20). In the structural
decomposition (Lemma 1), `c⁽ˡ⁾ = (|S⁽ˡ⁾| − |D⁽ˡ⁾|) / Σ_{j ∈ S⁽ˡ⁾} 1/w_j`.

Let `g` be differentiable, monotone and strictly convex, let all weights be positive and let `x*`
be an optimal solution of `𝒫^g`. For every level `l ≥ 1` of the decomposition (a connected
component `K` of `G′[D₁ \ D⁽⁰⁾, S \ S⁽⁰⁾]`) that contains a supply vertex, with
`S⁽ˡ⁾ = {j : j has level l}` and `D⁽ˡ⁾ = {i ∈ D₁ : i has level l}`,
`c⁽ˡ⁾ = (|S⁽ˡ⁾| − |D⁽ˡ⁾|) / Σ_{j ∈ S⁽ˡ⁾} 1/w_j`.

**Formalization Note.** Levels, `c⁽ˡ⁾` (`levelSlack`) and the level maps are the published
`TwoStageMatch.Decomposition`. A component without supply vertices (the case the published
Lemma 1 corrects) is excluded: there the formula reads `(0 − 1)/0` and is undefined. At level
`0`, `c⁽⁰⁾ = 0` and the formula does not hold in general, and the paper states the lemma for the
component levels `l ∈ [1 : L]` only (it is used for `l ∈ [L]` on pp.22 and ec12). -/
theorem lemma_3 {D₁ D₂ S : Type*} [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j)
    (x : D₁ → S → ℝ) (hx : IsOptimal I g x)
    (K : (residualGraph x).ConnectedComponent) (hK : ∃ j, levelS x j = some K) :
    levelSlack I.w x (some K) =
      (((Finset.univ.filter fun j => levelS x j = some K).card : ℝ) -
          ((Finset.univ.filter fun i => levelD x i = some K).card : ℝ)) /
        ∑ j ∈ Finset.univ.filter (fun j => levelS x j = some K), 1 / I.w j := by sorry

end TwoStageMatch.Supplement
