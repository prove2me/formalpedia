-- Prove2me | Theorems.Thm_ShockWear_CumDamage_proof34_transfer
-- name    : ShockWear.CumDamage.proof34_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:48:04.38272+00:00
-- url     : https://prove2.me/theorems/2278065c-041f-4bb0-b809-cafa5d7b4113
-- title:
--   Proof of (3.4), p. 633 — $\bar H(t) - e^{-(1-\zeta)\lambda t}$ inherits the sign change property of $\bar P_k - \zeta^k$
-- statement:
--   Let $\lambda > 0$, let $1 \ge \bar P_0 \ge \bar P_1 \ge \dots \ge 0$, let $\bar H$ be the shock survival function (2.1), and let $0 \le \zeta \le 1$. Then:
--
--   1. for every $t \ge 0$,
--   $$\bar H(t) - e^{-(1-\zeta)\lambda t} = \sum_{k=0}^\infty (\bar P_k - \zeta^k)\, e^{-\lambda t}\frac{(\lambda t)^k}{k!};$$
--   2. if the sequence $\bar P_k - \zeta^k$ ($k = 0, 1, \dots$) has at most one sign change, from $+$ to $-$ if one occurs, then the function $t \mapsto \bar H(t) - e^{-(1-\zeta)\lambda t}$ has at most one sign change on $[0, \infty)$, from $+$ to $-$ if one occurs.
--
--   This is the second step of the paper's proof of Theorem 3.1 (3.4), where it is obtained from the variation diminishing property of the totally positive kernel $K(k,t) = e^{-\lambda t}(\lambda t)^k/k!$.
--
--   **Formalization Note** The sign change property is stated on $t \ge 0$, where the series (2.1) defines $\bar H$; on $t < 0$ the paper sets $\bar H = 1$. $\bar P_k \ge 0$ is stated explicitly.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 633, proof of (3.4), second sentence

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem proof34_transfer (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 ≤ 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    (∀ t, 0 ≤ t →
      shockSurv lam P t - Real.exp (-((1 - ζ) * lam * t)) =
        ∑' k, (P k - ζ ^ k) * poisW lam t k) ∧
    (SignPMSeq (fun k => P k - ζ ^ k) →
      SignPM (fun t => shockSurv lam P t - Real.exp (-((1 - ζ) * lam * t))) (Set.Ici 0)) := by sorry

end ShockWear.CumDamage
