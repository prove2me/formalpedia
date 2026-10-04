-- Prove2me | Theorems.Thm_SecretaryWD_KnownOpt_accepting_contribution_ge
-- name    : SecretaryWD.KnownOpt.accepting_contribution_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:58:35.616652+00:00
-- url     : https://prove2.me/theorems/32541d71-bbe7-4f9d-870c-fb12efc81ff8
-- title:
--   Eq. (4.1) — the accepting permutations carry at least Z/2 of E[OPT]
-- statement:
--   Consider the discounted secretary problem with $n\ge1$ elements, values $v\ge0$ and discounts $d\ge0$, and let $Z$ be a real number with $Z\le\mathbf E[\mathrm{OPT}]$. Let $S_{acc}$ be the set of orders $\pi$ with $\max_i d(i)v(\pi(i))\ge Z/2$, on which the threshold algorithm with threshold $Z/2$ picks some element. Then their contribution to the expected offline optimum is at least $Z/2$:
--
--   $$L=\sum_{\pi\in S_{acc}}\frac1{n!}\max_{i=1}^n\{d(i)\,v(\pi(i))\}\;\ge\;\frac Z2.$$
--
--   This is the conclusion of the chain (4.1) in the proof of Theorem 4.7: on the rejecting orders the optimum is below $Z/2$, so almost all of $\mathbf E[\mathrm{OPT}]$ comes from the accepting ones.
--
--   **Formalization Note** $L$ is `acceptingContribution d v Z` and $S_{acc}$ is `acceptingPerms d v Z` of the mission's definition file.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 8, proof of Theorem 4.7, Eq. (4.1)

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

namespace SecretaryWD.KnownOpt

theorem accepting_contribution_ge {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (hZ : Z ≤ expectedOPT d v) :
    Z / 2 ≤ acceptingContribution d v Z := by sorry

end SecretaryWD.KnownOpt
