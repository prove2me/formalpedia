-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_3
-- name    : StaticProphetSec.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:55.339978+00:00
-- url     : https://prove2.me/theorems/48003417-46ec-47ae-b0de-870644da3df2
-- title:
--   Lemma 3 — $p_{n,k}\le k/n$
-- statement:
--   For $1\le k\le n$, let $p_{n,k}$ be a solution of
--
--   $$\mathbb E[\mathrm{UT}_k(\mathrm{Bin}(n,p_{n,k}))]=\gamma_k.$$
--
--   Then $p_{n,k}\le k/n$.
--
--   Since $\mathrm{AR}_k$ is weakly decreasing, this compares the binomial at $p_{n,k}$ with the binomial at $k/n$.
--
--   Differences from the source:
--
--   - encoding: "define $p_{n,k}$ to be the solution to (9)" → any $r\in[0,1]$ solving (9); reason: the source's $p_{n,k}$ is such an $r$
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 3, p.18, with (9)

import Mathlib
import Definitions.Def_StaticProphetSec_gamma
import Definitions.Def_StaticProphetSec_UT
import Definitions.Def_StaticProphetSec_pbE

namespace StaticProphetSec

/-- Lemma 3 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 3, p.18, with (9)): for `1 ≤ k ≤ n`, a solution
`r = p_{n,k}` of `E[UT_k(Bin(n, r))] = γ_k` satisfies `r ≤ k/n`. -/
theorem lemma_3 (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hr : pbE (UT k) (fun _ : Fin n => r) = gamma k) :
    r ≤ (k : ℝ) / (n : ℝ) := by sorry

end StaticProphetSec
