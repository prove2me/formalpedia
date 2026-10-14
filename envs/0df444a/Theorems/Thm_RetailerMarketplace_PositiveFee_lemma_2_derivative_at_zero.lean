-- Prove2me | Theorems.Thm_RetailerMarketplace_PositiveFee_lemma_2_derivative_at_zero
-- name    : RetailerMarketplace.PositiveFee.lemma_2_derivative_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:24.522382+00:00
-- url     : https://prove2.me/theorems/d2bf3804-4ed9-4c3e-8381-b2611e32e259
-- title:
--   Proof of Lemma 2, p. 8 — the right derivative of Π_M(k, ·) at f = 0 exists and is strictly positive
-- statement:
--   Let $c>0$, let $\lambda\in[\tfrac12,1]$ (Assumption 1) and $k\in[0,1]$, and let $\mu$ be a probability measure on $\mathbb R$ with $\mu((-\infty,c))=0$, absolutely continuous with respect to Lebesgue measure, and with $\int |v|\,d\mu(v)<\infty$. Write $\Pi_M(k,f)$ for the monopolist's profit at fee $f$: the supremum, over measurable sets $A$ of products with $\mu(A)\le k$, of the profit he earns by entering $A$ (SBM payoff $v-c$ on nonmarketplace products, SBMT payoff on marketplace products he enters, fee revenue $fv$ on marketplace products he leaves to the third-party seller). Assume that $k$ and $\lambda$ are not both equal to $1$.
--
--   Then $f\mapsto \Pi_M(k,f)$ has a right derivative at $f=0$, and it is strictly positive:
--   $$\frac{\partial \Pi_M}{\partial f}(k,0^+)=d\quad\text{for some } d>0 .$$
--
--   This is the step of the paper's proof of Lemma 2: raising the fee from zero increases the monopolist's profit at first order, so a zero fee cannot be optimal. At $f=0$ every product $v\ge c$ is a marketplace product (in the paper's notation $v_L=v_T=c$).
--
--   **Formalization Note.** The derivative is one-sided (within $[0,\infty)$ at $0$), since fees lie in $[0,1]$. The existence of the derivative is part of the claim, not a hypothesis. The exclusion of $k=\lambda=1$ is necessary: there $\pi_M^{SBMT}=v-c=\pi_M^{SBM}$, the monopolist supplies every product and $\Pi_M(1,f)=\int(v-c)\,d\mu$ for every $f$, so the derivative is $0$. The integrability of $v$ and $c>0$ are not stated in the paper and are added (the paper's profits are integrals against $G$ and its products lie in $[c,\infty)$ with $G(c)=0$).
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 8 (PDF p. 10), Proof of Lemma 2

import Mathlib
import Definitions.Def_RetailerMarketplace_PositiveFee_Model

open MeasureTheory

namespace RetailerMarketplace.PositiveFee

theorem lemma_2_derivative_at_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (c lam k : ℝ)
    (hc : 0 < c) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (hk : k ∈ Set.Icc (0 : ℝ) 1)
    (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume) (hint : Integrable (fun v : ℝ => v) μ)
    (hslip : ¬ (k = 1 ∧ lam = 1)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivWithinAt (fun f : ℝ => PiM μ c f lam k) d (Set.Ici 0) 0 := by sorry

end RetailerMarketplace.PositiveFee
