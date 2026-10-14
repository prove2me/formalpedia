-- Prove2me | Theorems.Thm_PlatformEntry_Protective_eq9_eq10_benchmarks
-- name    : PlatformEntry.Protective.eq9_eq10_benchmarks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:21.189912+00:00
-- url     : https://prove2.me/theorems/2e150f61-5bf4-4857-b0bb-51f9a18be479
-- title:
--   (9)–(10), PDF pp. 17–18 — e^B_N(a) and e^B_E(a) are the unique unconstrained maximizers of Π^S_N and Π^S_E
-- statement:
--   Let $f\in[0,1)$ and $c_S>1/2$, and let $a$ be any real base value. Then the first-best effort
--   $$e^B_N(a)=\frac{(1-f)a}{f+2c_S-1}\qquad(9)$$
--   is the unique maximizer over $e_S\in\mathbb R$ of the non-entry profit $\Pi^S_N(e_S)=(1-f)(a+e_S)^2/2-c_Se_S^2$. If moreover $(1-f)(1+4H)<4c_S$, then
--   $$e^B_E(a)=\frac{a(1-f)(1+4H)}{4c_S-(1-f)(1+4H)}\qquad(10)$$
--   is the unique maximizer over $e_S\in\mathbb R$ of the entry profit $\Pi^S_E(e_S)=(1/4+H)(1-f)(a+e_S)^2-c_Se_S^2$.
--
--   These are the seller's benchmark efforts when she assumes the platform never (respectively always) enters. Proposition 3 compares the seller's optimal effort with them.
--
--   **Formalization Note** The condition $(1-f)(1+4H)<4c_S$ is the strict concavity of $\Pi^S_E$, which the paper uses without stating it. It holds in the protective regime $H\le 1/4$ (given $f\ge0$, $c_S>1/2$) but can fail in the receptive regime. "Unique" is written as a strict inequality against every other effort.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF pp. 17–18, (9)–(10); 'unique unconstrained maximizers' in Online Supplement, Appendix A, proof of Proposition 3, PDF p. 36

import Mathlib
import Definitions.Def_PlatformEntry_Protective_Model

namespace PlatformEntry.Protective

/-- (9)–(10), PDF pp. 17–18: e^B_N(a) and e^B_E(a) are the unique unconstrained maximizers
of Π^S_N and Π^S_E. The second part assumes the concavity condition (1 − f)(1 + 4H) < 4c_S. -/
theorem eq9_eq10_benchmarks (δ f β cS a : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) (hcS : 1 / 2 < cS) :
    (∀ e : ℝ, e ≠ eBN f cS a → PlatformEntry.Regimes.profitN δ f β cS a e < PlatformEntry.Regimes.profitN δ f β cS a (eBN f cS a)) ∧
      ((1 - f) * (1 + 4 * PlatformEntry.Regimes.H δ f β) < 4 * cS →
        ∀ e : ℝ, e ≠ eBE δ f β cS a →
          PlatformEntry.Regimes.profitE δ f β cS a e < PlatformEntry.Regimes.profitE δ f β cS a (eBE δ f β cS a)) := by sorry

end PlatformEntry.Protective
