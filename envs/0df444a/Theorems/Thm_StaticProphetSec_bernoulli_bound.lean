-- Prove2me | Theorems.Thm_StaticProphetSec_bernoulli_bound
-- name    : StaticProphetSec.bernoulli_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:30.170977+00:00
-- url     : https://prove2.me/theorems/42b64282-e6e2-4896-b8e0-2880c3ab77cf
-- title:
--   (7)–(13), p.18 — $\mathbb E[\mathrm{UT}_k(D_q)]=\gamma_k$ implies $\mathbb E[\mathrm{AR}_k(D_q)]\ge\gamma_k$
-- statement:
--   For all $k\ge1$, all $n$ and all $q\in[0,1]^n$ with $\mathbb E[\mathrm{UT}_k(D_q)]=\gamma_k$,
--
--   $$\mathbb E[\mathrm{AR}_k(D_q)]\ge\gamma_k.$$
--
--   Equivalently $\Phi_n(\mathrm{AR}_k,\mathrm{UT}_k,\gamma_k)\ge\gamma_k$. This is the chain (8), (10), (11), (12), (13), and it closes the proof of Theorem 2.
--
--   Differences from the source:
--
--   - encoding: $\Phi_n(\mathrm{AR}_k,\mathrm{UT}_k,\gamma_k)\ge\gamma_k$ via the chain → a bound on every feasible point, for every $n$; reason: a lower bound on a min is a bound on every feasible point; the source's padding step covers small $n$
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, (7)–(13), p.18

import Mathlib
import Definitions.Def_StaticProphetSec_gamma
import Definitions.Def_StaticProphetSec_UT
import Definitions.Def_StaticProphetSec_AR
import Definitions.Def_StaticProphetSec_pbE

namespace StaticProphetSec

/-- The Bernoulli bound (Arnosti & Ma, arXiv:2108.12893v2, (7)–(13), p.18): for every `n`, every
feasible point of `Φ_n(AR_k, UT_k, γ_k)` has objective value at least `γ_k`: if `q ∈ [0, 1]^n`
and `E[UT_k(D_q)] = γ_k`, then `E[AR_k(D_q)] ≥ γ_k`. -/
theorem bernoulli_bound (k n : ℕ) (hk : 1 ≤ k) (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hq' : pbE (UT k) q = gamma k) :
    gamma k ≤ pbE (AR k) q := by sorry

end StaticProphetSec
