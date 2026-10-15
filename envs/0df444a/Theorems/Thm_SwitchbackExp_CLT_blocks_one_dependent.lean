-- Prove2me | Theorems.Thm_SwitchbackExp_CLT_blocks_one_dependent
-- name    : SwitchbackExp.CLT.blocks_one_dependent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:14.564143+00:00
-- url     : https://prove2.me/theorems/7c97d825-3e70-4346-8eb5-831615977f06
-- title:
--   EC.4.4, proof of Theorem 3, p. ec27 — under 𝕋* the block errors X_i = 𝟙̄_{i−1}, i = 1, …, n − 1, are 1-dependent
-- statement:
--   Let $m\ge1$, $n\ge4$, $T=nm$, and consider the optimal design $\mathbb T^*=\{1,2m+1,\dots,(n-2)m+1\}$ with independent fair coins. For $i=1,\dots,n-1$ let $X_i=\bar{\mathbb 1}_{i-1}$ be the block error of EC.4.1, viewed as a function of the coin flips. Then
--   $$X_1,X_2,\dots,X_{n-1}\ \text{is a $1$-dependent sequence:}$$
--   for all $r<s\le n-1$ with $s-r>1$, the vectors $(X_1,\dots,X_r)$ and $(X_s,\dots,X_{n-1})$ are independent.
--
--   This is the dependence structure required to apply the Romano–Wolf central limit theorem (Lemma EC.1) with $d=n-1$ and $\phi=1$.
--
--   **Formalization Note** The paper states 1-dependence for the scaled variables $X_{n,i}=\bar{\mathbb 1}_{i-1}/((n-1)m)$; the positive constant scaling does not affect independence, so the statement is made for $\bar{\mathbb 1}_{i-1}$ directly. The block errors are built from $Y_t(\mathbf 1_{m+1})$ and $Y_t(\mathbf 0_{m+1})$ only, so no assumption on the potential outcomes is needed.
-- source:
--   arXiv:2009.00148v4, EC.4.4, proof of Theorem 3, p. ec27, first paragraph

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_CLT_Setting
import Definitions.Def_SwitchbackExp_CLT_PhiDependent

open SwitchbackExp.Design

namespace SwitchbackExp.CLT

/-- EC.4.4, proof of Theorem 3, p. ec27: under the optimal design with `T = n m`, `n ≥ 4`, the block
errors `X_i = 𝟙̄_{i−1}`, `i = 1, …, n − 1`, viewed as functions of the fair coins, are 1-dependent. -/
theorem blocks_one_dependent (m n : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (Y : Outcomes) :
    IsPhiDependent (coinMeasure m n) 1 (n - 1)
      (fun i c => blockErr m (optPoints m n) half Y (i - 1) (pathOf (optPoints m n) c)) := by sorry

end SwitchbackExp.CLT
