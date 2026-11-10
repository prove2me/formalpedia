-- Prove2me | Theorems.Thm_RandOrderKnapGAP_Integral_eq_B_51
-- name    : RandOrderKnapGAP.Integral.eq_B_51
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:59.299208+00:00
-- url     : https://prove2.me/theorems/572afd2e-292e-4032-84da-bb5738e2046a
-- title:
--   §B.9.2, Eq. (B.51) — moments of the weight of a uniform $k'$-subset (sampling without replacement)
-- statement:
--   Let $L\ge2$ identities carry weights $c_j\ge0$, with $C_0=\sum_jc_j$ and $J_0=\sum_jc_j^2$. Let $Y$ be the total weight of a uniformly random $k'$-element subset ($0\le k'\le L$) and $\tau=k'/L$. Each identity is included with probability $\tau$, two distinct identities together with probability $k'(k'-1)/(L(L-1))$, and
--   $$\mathbb E[Y]=\tau C_0,\qquad \mathbb E[Y^2]=\tau^2C_0^2+\tau(1-\tau)J_0-\frac{\tau(1-\tau)}{L-1}\big(C_0^2-J_0\big)\le\tau^2C_0^2+\tau(1-\tau)J(C_0),$$
--   where the last inequality holds when every weight is at most $\delta$ and $J$ is the function of Lemma B.7.
--
--   The identity replaces the independent-inclusion calculation of the limiting analysis by its exact finite-prefix counterpart.
--
--   Differences from the source:
--   - generalization: weights: zero on non-comparator identities, the small comparator sizes (≤ δ = 1/3) on the others → any nonnegative weights c : Fin L → ℝ; the final inequality for any δ > 0 with every c_j ≤ δ; reason: the computation uses only nonnegativity, and J(C₀) ≥ J₀ only needs c_j ∈ [0, δ]; the paper's weights are an instance
--   - encoding: Y the weight of a uniformly random k′-element subset of the L remaining identities → averages over Finset.powersetCard k′ (Finset.univ : Finset (Fin L)), divided by binom(L, k′); hypotheses 2 ≤ L and k′ ≤ L; reason: a uniform k′-subset is the uniform average over the binom(L, k′) subsets; L ≥ 2 keeps L − 1 > 0 as in the paper
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), p. 58 (PDF 60), §B.9.2, Eq. (B.51)

import Mathlib
import Definitions.Def_RandOrderKnapGAP_Integral_Constants

open scoped BigOperators

namespace RandOrderKnapGAP.Integral

/-- **§B.9.2, Eq. (B.51)**, p. 58. `L ≥ 2` identities carry nonnegative weights `c_j`, with
`C₀ = ∑ c_j` and `J₀ = ∑ c_j²`. Let `Y` be the total weight of a uniformly random `k'`-element
subset (`k' ≤ L`) and `τ = k'/L`. Each identity is included with probability `τ`, two distinct
identities together with probability `k'(k'−1)/(L(L−1))`, `E[Y] = τ C₀` and
`E[Y²] = τ²C₀² + τ(1−τ)J₀ − (τ(1−τ)/(L−1))(C₀² − J₀)`; if moreover every weight is at most
`δ` (`δ > 0`), then `E[Y²] ≤ τ²C₀² + τ(1−τ)J(C₀)`. Expectations are averages over the
`binom L k'` subsets. -/
theorem eq_B_51 (L k' : ℕ) (hL : 2 ≤ L) (hk : k' ≤ L) (c : Fin L → ℝ) (hc : ∀ j, 0 ≤ c j) :
    let τ : ℝ := (k' : ℝ) / (L : ℝ)
    let C₀ : ℝ := ∑ j, c j
    let J₀ : ℝ := ∑ j, c j ^ 2
    let subsets : Finset (Finset (Fin L)) := Finset.univ.powersetCard k'
    let M : ℝ := (Nat.choose L k' : ℝ)
    let Y : Finset (Fin L) → ℝ := fun S => ∑ j ∈ S, c j
    (∀ j, ((subsets.filter (fun S => j ∈ S)).card : ℝ) / M = τ) ∧
    (∀ j j', j ≠ j' → ((subsets.filter (fun S => j ∈ S ∧ j' ∈ S)).card : ℝ) / M
        = (k' : ℝ) * ((k' : ℝ) - 1) / ((L : ℝ) * ((L : ℝ) - 1))) ∧
    (∑ S ∈ subsets, Y S) / M = τ * C₀ ∧
    (∑ S ∈ subsets, Y S ^ 2) / M
        = τ ^ 2 * C₀ ^ 2 + τ * (1 - τ) * J₀ - τ * (1 - τ) / ((L : ℝ) - 1) * (C₀ ^ 2 - J₀) ∧
    (∀ δ : ℝ, 0 < δ → (∀ j, c j ≤ δ) →
      (∑ S ∈ subsets, Y S ^ 2) / M ≤ τ ^ 2 * C₀ ^ 2 + τ * (1 - τ) * Jbound δ C₀) := by sorry

end RandOrderKnapGAP.Integral
