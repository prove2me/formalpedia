-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_proposition_2
-- name    : RetailerMarketplace.Entry.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:41.019393+00:00
-- url     : https://prove2.me/theorems/d67b6dc8-c6fe-42cd-bf78-054a12733e0c
-- title:
--   Proposition 2, p. 7 — below the capacity threshold k̲ M enters [v_K, ∞) (Mode I); above it he also enters [v_L, v_T) (Mode II)
-- statement:
--   Let $c>0$ be the unit cost, $f\in[0,1)$ the ad valorem fee, $\lambda\in[\tfrac12,1]$ the share of consumers $M$ can steer (Assumption 1), and $k\in[0,1]$ $M$'s capacity. Let $\mu$ be the distribution of product valuations: a probability measure on $\mathbb R$ with $\mu((-\infty,c))=0$, absolutely continuous with respect to Lebesgue measure, with $\int|v|\,d\mu<\infty$, and charging every nonempty open interval of $[c,\infty)$; $G(v)=\mu((-\infty,v])$. Third-party sellers enter the products with $v\ge v_T=c/(1-f)$, and $M$ chooses an allocation: any measurable set $A$ of products with $\mu(A)\le k$, maximizing his total profit (SBM profits on $A$ below $v_T$, SBMT profits on $A$ above $v_T$, fee revenue on the marketplace products outside $A$).
--
--   Then there is a threshold $\underline k\in[0,1]$, namely $\underline k=1-G(v^*)$, such that
--   1. **Mode I** ($k\le\underline k$): an optimal allocation exists and is unique up to $\mu$-null sets; it is $\emptyset$ if $k=0$ and otherwise
--   $$A=[v_K,\infty)\quad\text{with}\quad 1-G(v_K)=k,\ v_K\ge v_T,$$
--   so products in $[v_T,v_K)$ are supplied under SBT and products in $[v_K,\infty)$ under SBMT;
--   2. **Mode II** ($k>\underline k$): there are $c\le v_L\le v_T\le v_H$ with
--   $$\pi_M^{SBM}(v_L)=\Delta\pi_M^{SBMT-SBT}(v_H),\qquad (1-G(v_H))+(G(v_T)-G(v_L))=k,$$
--   such that $A=[v_L,v_T)\cup[v_H,\infty)$ is an optimal allocation and every optimal allocation equals it up to a $\mu$-null set; so products in $[v_L,v_T)$ are supplied under SBM, in $[v_T,v_H)$ under SBT, and in $[v_H,\infty)$ under SBMT.
--
--   This is the paper's characterization of the two marketplace modes: with little capacity the monopolist competes only in the most valuable marketplace products; with more capacity he also monopolizes products no third party supplies.
--
--   **Formalization Note** Products below $v_T$ are not marketplace products ($T$ stays out), so an allocation avoiding them leaves them unsupplied. $f<1$ is assumed because $v_T=c/(1-f)$ is finite only then; the foreclosed case $f=1$ is not covered. $c>0$, integrability of $v$ (so that profits are finite) and full support on $[c,\infty)$ (the reading of $v_K=G^{-1}(1-k)$ in (3)) are added hypotheses. At $k=0$, $v_K=G^{-1}(1)=\infty$ and the optimal allocation is empty. At $k=1$ the Mode II thresholds are $v_L=c$, $v_H=v_T$, so the bounds are closed. At $f=0$, $\underline k=1$ and Mode II is vacuous, as in the paper.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 7 (PDF p. 9), Proposition 2; display (3); proof pp. 13–15 (PDF pp. 15–17)

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

open MeasureTheory

namespace RetailerMarketplace.Entry

/-- Proposition 2: there is a capacity threshold `k̲ ∈ [0, 1]` (namely `1 - G(v*)`) such that M's
optimal capacity allocations (unique up to `μ`-null sets) are
1. (Mode I, `k ≤ k̲`) the top products `[v_K, ∞)` with `1 - G(v_K) = k` and `v_K ≥ v_T`, so that
   `[v_T, v_K)` is SBT and `[v_K, ∞)` is SBMT (no product at all when `k = 0`);
2. (Mode II, `k > k̲`) `[v_L, v_T) ∪ [v_H, ∞)` with `c ≤ v_L ≤ v_T ≤ v_H`, where `v_L, v_H` equalize
   `π_M^SBM(v_L) = Δπ_M^{SBMT-SBT}(v_H)` and use all capacity, so that `[v_L, v_T)` is SBM,
   `[v_T, v_H)` is SBT and `[v_H, ∞)` is SBMT. -/
theorem proposition_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam k : ℝ) (hc : 0 < c)
    (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hk : k ∈ Set.Icc (0 : ℝ) 1) (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume)
    (hint : Integrable (fun v : ℝ => v) μ)
    (hfull : ∀ a b : ℝ, c ≤ a → a < b → 0 < μ (Set.Ioo a b)) :
    ∃ k₀ ∈ Set.Icc (0 : ℝ) 1, k₀ = kbar μ c f lam ∧
      (k ≤ k₀ →
        ∃ U : Set ℝ,
          ((k = 0 ∧ U = ∅) ∨
            ∃ vK : ℝ, vT c f ≤ vK ∧ 1 - G μ vK = k ∧ U = Set.Ici vK) ∧
          IsOptimalAlloc μ c f lam k U ∧
          ∀ A : Set ℝ, IsOptimalAlloc μ c f lam k A → A =ᵐ[μ] U) ∧
      (k₀ < k →
        ∃ vL vH : ℝ, c ≤ vL ∧ vL ≤ vT c f ∧ vT c f ≤ vH ∧
          piSBM c vL = dPi c f lam vH ∧
          (1 - G μ vH) + (G μ (vT c f) - G μ vL) = k ∧
          IsOptimalAlloc μ c f lam k (Set.Ico vL (vT c f) ∪ Set.Ici vH) ∧
          ∀ A : Set ℝ, IsOptimalAlloc μ c f lam k A →
            A =ᵐ[μ] (Set.Ico vL (vT c f) ∪ Set.Ici vH : Set ℝ)) := by sorry

end RetailerMarketplace.Entry
