-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_lemma_4
-- name    : ThirdPartyPricing.General.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:13.777933+00:00
-- url     : https://prove2.me/theorems/f5f34c36-59fe-4b05-a546-1ced513dd2dd
-- title:
--   Lemma 4, p. 22 — if φ̃(a, p̃) < pᴹ(a) then the algorithm's price φ̃(a, p̃) is increasing in β
-- statement:
--   Work in the model of §3 under the standing assumptions. For $\beta\in[0,1]$, $\tilde p\in[c,p^{\max}]$ and $a\in[a_0,a_1]$, let $\tilde\phi(a,\tilde p,\beta)$ be a maximizer
--   $$\tilde\phi(a,\tilde p,\beta)\in\arg\max_{p\in[c,p^{\max}]}(1-\beta)\pi_1(p,\tilde p,a)+\beta\pi_1(p,p,a).$$
--   Fix $a$, $\tilde p$ and $0\le\beta_1<\beta_2\le 1$. If $\tilde\phi(a,\tilde p,\beta)<p^M(a)$ for every $\beta\in[\beta_1,\beta_2)$, then
--   $$\tilde\phi(a,\tilde p,\beta_1)<\tilde\phi(a,\tilde p,\beta_2).$$
--
--   Below the joint-profit-maximizing price, giving more weight to the event that the algorithm faces itself raises the price it sets; this is the second step of the proof of Theorem 2.
--
--   **Formalization Note** The paper proves a local statement (an $\varepsilon>0$ at each $\beta'$) and applies it on an interval; the hypothesis $\tilde\phi<p^M(a)$ is therefore required along the half-open interval $[\beta_1,\beta_2)$; at $\beta_2=1$ the maximizer equals $p^M(a)$, so a strict below-$p^M$ condition there would be impossible. $\tilde\phi$ is any selection with the argmax property.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 22, Lemma 4

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem lemma_4 (P : Primitives) (hP : P.Standing) (phiT : ℝ → ℝ → ℝ → ℝ) (hphiT : ∀ β ∈ Set.Icc (0:ℝ) 1, ∀ pt ∈ P.prices, ∀ a ∈ P.states, phiT β pt a ∈ P.prices ∧ IsMaxOn (P.tpObj β pt a) P.prices (phiT β pt a)) (a : ℝ) (ha : a ∈ P.states) (pt : ℝ) (hpt : pt ∈ P.prices) (β₁ β₂ : ℝ) (h0 : 0 ≤ β₁) (h12 : β₁ < β₂) (h1 : β₂ ≤ 1) (hbelow : ∀ β ∈ Set.Ico β₁ β₂, phiT β pt a < P.pM a) : phiT β₁ pt a < phiT β₂ pt a := by sorry
end ThirdPartyPricing.General
