-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_eq_E_1
-- name    : VerticalOwnership.CheapTalk.eq_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:33.352026+00:00
-- url     : https://prove2.me/theorems/daea3eeb-2893-456e-aacd-0c69f201a8d1
-- title:
--   (E.1), p. 45 — (13) holds iff β ≥ β̳, and the numerator and denominator of β̳ are positive
-- statement:
--   In the model of the mission, write $K_L=\mu_L+F^{-1}(z_s)$ and $K_H=\mu_H+F^{-1}(z_s)$. The retailer's operational gain from pretending to be a high type and the supplier's loss from being misled are both positive:
--   $$\pi_r(0,K_H\mid\mu_L)-\pi_r(0,K_L\mid\mu_L)>0,\qquad \pi_s(K_L\mid\mu_L,0)-\pi_s(K_H\mid\mu_L,0)>0.$$
--   Moreover, for every $\beta\in[0,1]$, condition (13), $v_r(0,K_L\mid\mu_L)\ge v_r(0,K_H\mid\mu_L)$, holds if and only if
--   $$\beta\ \ge\ \underline{\underline{\beta}}=\frac{\pi_r(0,K_H\mid\mu_L)-\pi_r(0,K_L\mid\mu_L)}{\pi_s(K_L\mid\mu_L,0)-\pi_s(K_H\mid\mu_L,0)}.$$
--
--   This turns the low type's truth-telling constraint into a threshold on the ownership share.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 45, Appendix E, Proof of Theorem 2, (E.1)

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem eq_E_1 (M : Model) (hM : M.Standing) :
    0 < M.πr M.μL 0 M.KH - M.πr M.μL 0 M.KL ∧
    0 < M.πs M.μL 0 M.KL - M.πs M.μL 0 M.KH ∧
    ∀ β ∈ Set.Icc (0 : ℝ) 1, (M.cond13 β ↔ M.betaCT ≤ β) := by sorry

end VerticalOwnership.CheapTalk
