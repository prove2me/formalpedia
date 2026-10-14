-- Prove2me | Theorems.Thm_RetailerMarketplace_PositiveFee_lemma_2
-- name    : RetailerMarketplace.PositiveFee.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:30.72031+00:00
-- url     : https://prove2.me/theorems/f9ae36d5-cfc6-4a7f-be1b-69209f5bf232
-- title:
--   Lemma 2, p. 7 — every fee in [0, 1] that maximises the monopolist's profit Π_M(k, f) is strictly positive, f* > 0
-- statement:
--   Let $c>0$ be the firms' marginal cost, $\lambda\in[\tfrac12,1]$ the share of consumers the monopolist can steer (Assumption 1), and $k\in[0,1]$ his assortment capacity. Let the product valuations be distributed according to a probability measure $\mu$ on $\mathbb R$ with $\mu((-\infty,c))=0$, absolutely continuous with respect to Lebesgue measure (the CDF $G$ has a density), and with $\int|v|\,d\mu(v)<\infty$. For a fee $f\in[0,1]$ let $\Pi_M(k,f)$ be the monopolist's equilibrium profit: the supremum, over all measurable sets $A$ of products with $\mu(A)\le k$, of his profit when he enters exactly $A$ and the third-party sellers enter exactly the products with $v(1-f)\ge c$ (Lemma 1), with the per-market payoffs of Proposition 1. Assume that $k$ and $\lambda$ are not both equal to $1$.
--
--   If $f^*\in[0,1]$ maximises the monopolist's profit over all fees,
--   $$\Pi_M(k,f)\le\Pi_M(k,f^*)\quad\text{for all } f\in[0,1],$$
--   then
--   $$f^*>0 .$$
--
--   This is Lemma 2 of the paper: the monopolist always charges a strictly positive ad valorem fee. It holds for every capacity and every admissible steering share, and it underlies the paper's analysis of the optimal fee (Proposition 3) and of fee regulation.
--
--   **Formalization Note.** The statement concerns every maximiser; it does not assert that a maximiser exists (the paper does not claim existence in Lemma 2). $\Pi_M$ is the value of the monopolist's Stage-2 allocation problem over all measurable allocations; by Proposition 2 it coincides with the paper's closed form (4). Added hypotheses, all disclosed: $c>0$ and $\int|v|\,d\mu<\infty$, which the paper uses implicitly; and $\neg(k=1\wedge\lambda=1)$. The last is necessary: at $k=\lambda=1$ the SBMT and SBM payoffs coincide, the monopolist supplies every product, and $\Pi_M(1,f)=\int(v-c)\,d\mu$ for every $f$, so $f^*=0$ is optimal and the printed claim fails (numerically, with $G(v)=1-e^{-2(v-1)}$, $c=1$: $\Pi_M(1,f)=0.5$ for $f=0,0.3,0.9$).
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 7 (PDF p. 9), Lemma 2

import Mathlib
import Definitions.Def_RetailerMarketplace_PositiveFee_Model

open MeasureTheory

namespace RetailerMarketplace.PositiveFee

theorem lemma_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam k : ℝ)
    (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) (hint : Integrable (fun v : ℝ => v) μ)
    (hslip : ¬ (k = 1 ∧ lam = 1))
    (fstar : ℝ) (hfstar : fstar ∈ Set.Icc (0 : ℝ) 1)
    (hopt : ∀ f ∈ Set.Icc (0 : ℝ) 1, PiM μ c f lam k ≤ PiM μ c fstar lam k) :
    0 < fstar := by sorry

end RetailerMarketplace.PositiveFee
