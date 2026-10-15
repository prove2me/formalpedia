-- Prove2me | Theorems.Thm_SwitchbackExp_CLT_lemma_2
-- name    : SwitchbackExp.CLT.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:04.04796+00:00
-- url     : https://prove2.me/theorems/75c36782-70ba-4a4f-9b38-0d46b3441fc4
-- title:
--   Lemma 2, p. 16 — under the optimal design with T = nm, n ≥ 4, Var(τ̂_m) is given in closed form by (10)
-- statement:
--   Let $m\ge1$, $n\ge4$ and $T=nm$, and let the potential outcomes satisfy Assumptions 1–2. Under the optimal design $\mathbb T^*=\{1,2m+1,\dots,(n-2)m+1\}$ with fair coins, the variance of the Horvitz–Thompson estimator is
--   $$\begin{aligned}\mathrm{Var}(\hat\tau_m)=\frac1{(T-m)^2}\Big\{&\bar Y_0(\mathbf 1_{m+1})^2+\bar Y_0(\mathbf 0_{m+1})^2+2\bar Y_0(\mathbf 1_{m+1})\bar Y_0(\mathbf 0_{m+1})\\&+\sum_{k=1}^{n-3}\big[3\bar Y_k(\mathbf 1_{m+1})^2+3\bar Y_k(\mathbf 0_{m+1})^2+2\bar Y_k(\mathbf 1_{m+1})\bar Y_k(\mathbf 0_{m+1})\big]\\&+\bar Y_{n-2}(\mathbf 1_{m+1})^2+\bar Y_{n-2}(\mathbf 0_{m+1})^2+2\bar Y_{n-2}(\mathbf 1_{m+1})\bar Y_{n-2}(\mathbf 0_{m+1})\\&+\sum_{k=0}^{n-3}2\big[\bar Y_k(\mathbf 1_{m+1})+\bar Y_k(\mathbf 0_{m+1})\big]\big[\bar Y_{k+1}(\mathbf 1_{m+1})+\bar Y_{k+1}(\mathbf 0_{m+1})\big]\Big\}.\end{aligned}\tag{10}$$
--   Here $\bar Y_k(\mathbf 1_{m+1})$ and $\bar Y_k(\mathbf 0_{m+1})$ are the sums of $Y_t(\mathbf 1_{m+1})$, respectively $Y_t(\mathbf 0_{m+1})$, over the block $t=(k+1)m+1,\dots,(k+2)m$.
--
--   The formula is the normalising variance of the central limit theorem (Theorem 3) and the starting point of the conservative variance bound of Corollary 1.
--
--   **Formalization Note** The paper lists Assumptions 1–3; (10) is an identity that does not use the bound $B$ of Assumption 3, so Assumption 3 is omitted. The right-hand side is the definition `lemma2Var m n Y`.
-- source:
--   arXiv:2009.00148v4, Lemma 2 and (10), p. 16; proof EC.4.2, pp. ec25–ec26

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_CLT_Setting

open SwitchbackExp.Design

namespace SwitchbackExp.CLT

/-- Lemma 2, p. 16: under Assumptions 1–2 and the optimal design with `T = n m`, `n ≥ 4`, the variance
of the Horvitz–Thompson estimator is (10). -/
theorem lemma_2 (m n : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (Y : Outcomes)
    (hA1 : NonAnticipating (n * m) Y) (hA2 : Carryover m (n * m) Y) :
    htVar m (n * m) (optPoints m n) half Y = lemma2Var m n Y := by sorry

end SwitchbackExp.CLT
