-- Prove2me | Theorems.Thm_SeqLoss_FixedFraction_fixedFraction_isRule
-- name    : SeqLoss.FixedFraction.fixedFraction_isRule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:15.667033+00:00
-- url     : https://prove2.me/theorems/849a66e3-df89-4400-b557-3ca4512cce19
-- title:
--   §3, p. 8 — for $\lambda\in[0,1]$ the fixed-fraction formula $\varphi^\lambda$ is a (continuous) rule
-- statement:
--   Let $\lambda\in[0,1]$. The fixed-fraction rule
--   $$\varphi^\lambda_1(\ell)=\lambda\ell_1+(1-\lambda)L,\qquad \varphi^\lambda_i(\ell)=\lambda\ell_i\ (i\ge 2)$$
--   is a rule: for every $n$ and every loss vector $\ell\in L^n$, $\varphi^\lambda(\ell)$ is an allocation of $\ell$ (liabilities non-negative, every initial group $1,\dots,m$ with $m<n$ pays at least $\ell_1+\dots+\ell_m$, liabilities sum to $L$), and $\varphi^\lambda(a\ell)\to\varphi^\lambda(\ell)$ as $a\to 1$.
--
--   The paper restricts $\lambda$ to $[0,1]$ "to ensure non-negative liabilities". This is what makes the fixed-fraction rules admissible in Theorem 1.
--
--   **Formalization Note.** `IsRule` is the Setting's notion: allocation and continuity on every loss vector, for every $n$ (including $n=0$).
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, p. 8, §3, sentence before Definition 1

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting

namespace SeqLoss.FixedFraction

theorem fixedFraction_isRule (lam : ℝ) (hlam : lam ∈ Set.Icc (0:ℝ) 1) :
    IsRule (fixedFraction lam) := by sorry

end SeqLoss.FixedFraction
