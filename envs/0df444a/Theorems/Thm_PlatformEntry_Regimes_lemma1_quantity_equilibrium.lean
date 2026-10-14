-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_lemma1_quantity_equilibrium
-- name    : PlatformEntry.Regimes.lemma1_quantity_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:48.707456+00:00
-- url     : https://prove2.me/theorems/5d2b8990-7a22-45ef-bbfa-a9cf5063170d
-- title:
--   Lemma 1, PDF p. 11 — the unique Cournot quantities after entry
-- statement:
--   Let $(\delta,f,\beta)$ lie in the standing ranges $\delta\in[0,1]$, $f\in[0,1)$, $\beta\in[0,1]$, let the value carried into stage 2 be $a + e_S > 0$, let the platform's effort be $e_P \ge 0$, and let $K$ be any entry cost. Then $(q_S, q_P)$ is an equilibrium of the stage-2 quantity game after entry (each party's quantity is a best response over $[0,\infty)$ to the other's, with payoffs (3) and (4)) if and only if
--
--   $$
--   q_S^* = \left[\frac{2-\beta}{4-\beta^2(1+f)}(a+e_S+e_P) - \frac{2(1-\delta)}{4-\beta^2(1+f)}\,e_P\right]^+, \qquad q_P^* = \frac{a + e_S + e_P - \beta(1+f)\,q_S^*}{2}.
--   $$
--
--   In particular the quantity equilibrium exists and is unique. This is the first step of the backward induction: it reduces the platform's effort problem to a problem in $e_P$ alone.
--
--   **Formalization Note** $[x]^+$ is $\max(x,0)$. The paper's "the equilibrium quantity decisions are" is formalized as an equivalence, which states both existence and uniqueness. The hypotheses $a + e_S > 0$ and $e_P \ge 0$ are not written in the lemma; they are the economic setting (a positive product value, a nonnegative effort) and make $q_P^* \ge 0$.
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), PDF p. 11, Lemma 1; proof Online Supplement, Appendix A, PDF p. 32

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem lemma1_quantity_equilibrium (δ f β K a eS eP qS qP : ℝ) (hbox : InBox δ f β)
    (hA : 0 < a + eS) (heP : 0 ≤ eP) :
    IsQuantityEq δ f β K (a + eS) eP qS qP ↔
      (qS = max ((2 - β) / (4 - β ^ 2 * (1 + f)) * (a + eS + eP)
                  - 2 * (1 - δ) / (4 - β ^ 2 * (1 + f)) * eP) 0 ∧
        qP = (a + eS + eP - β * (1 + f) * qS) / 2) := by sorry

end PlatformEntry.Regimes
