-- Prove2me | Theorems.Thm_ThirdPartyPricing_General_phiT_continuous_increasing
-- name    : ThirdPartyPricing.General.phiT_continuous_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:01.871511+00:00
-- url     : https://prove2.me/theorems/2d78e308-4935-4857-a88e-a39993c1b5ac
-- title:
--   Proof of Theorem 1, p. 18 — the algorithm's best response φ̃(a, p̃) is continuous and increasing in the rival's price p̃
-- statement:
--   Work in the model of §3 under the standing assumptions, and fix an adoption probability $\beta\in[0,1)$. For a non-adopter price $\tilde p\in[c,p^{\max}]$ and a demand state $a\in[a_0,a_1]$, let $\tilde\phi(a,\tilde p)$ be a maximizer (18)
--   $$\tilde\phi(a,\tilde p)\in\arg\max_{p\in[c,p^{\max}]}\ (1-\beta)\pi_1(p,\tilde p,a)+\beta\pi_1(p,p,a).$$
--   Then, for every demand state $a$, the map $\tilde p\mapsto\tilde\phi(a,\tilde p)$ is continuous on $[c,p^{\max}]$ and strictly increasing there.
--
--   This is the first step of the proof of existence (Theorem 1): it shows that the algorithm designed against a higher rival price charges a higher price.
--
--   **Formalization Note** $\tilde\phi$ is any selection with the argmax property (it is unique by strict concavity). The statement is restricted to $\beta<1$: at $\beta=1$ the objective does not depend on $\tilde p$, $\tilde\phi(a,\cdot)\equiv p^M(a)$, and strictness fails; the paper's argument (via (6), multiplied by $1-\beta$) uses $\beta<1$ implicitly.
-- source:
--   Harrington, Third Party Pricing Algorithms and the Intensity of Competition, working paper (3 November 2020), p. 18, proof of Theorem 1, (18), (20)

import Mathlib
import Definitions.Def_ThirdPartyPricing_General_Model

namespace ThirdPartyPricing.General
open Primitives
theorem phiT_continuous_increasing (P : Primitives) (hP : P.Standing) (β : ℝ) (hβ : β ∈ Set.Ico (0:ℝ) 1) (phiT : ℝ → ℝ → ℝ) (hphiT : ∀ pt ∈ P.prices, ∀ a ∈ P.states, phiT pt a ∈ P.prices ∧ IsMaxOn (P.tpObj β pt a) P.prices (phiT pt a)) (a : ℝ) (ha : a ∈ P.states) : ContinuousOn (fun pt => phiT pt a) P.prices ∧ StrictMonoOn (fun pt => phiT pt a) P.prices := by sorry
end ThirdPartyPricing.General
