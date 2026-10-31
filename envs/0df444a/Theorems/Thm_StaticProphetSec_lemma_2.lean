-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_2
-- name    : StaticProphetSec.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:20.332264+00:00
-- url     : https://prove2.me/theorems/3b2c9e06-d0e3-452d-a222-718cdf43461c
-- title:
--   Lemma 2 — $\Phi_n(\mathrm{AR}_k,\mathrm{UT}_k,\phi)$ has an optimal solution with all $p_i$ equal
-- statement:
--   For all $k\ge1$ and $n>k$ and all $\phi\in(0,1)$, the optimization problem
--
--   $$\Phi_n(\mathrm{AR}_k,\mathrm{UT}_k,\phi)=\min_{q\in[0,1]^n}\mathbb E[\mathrm{AR}_k(D_q)]\quad\text{s.t.}\quad\mathbb E[\mathrm{UT}_k(D_q)]=\phi$$
--
--   has an optimal solution in which all $q_i$ are equal.
--
--   This reduces the Bernoulli optimization problem to a one-parameter binomial family.
--
--   Differences from the source:
--
--   - encoding: "has an optimal solution in which all $p_i$ are equal" → there is $r\in[0,1]$ such that the constant vector $r$ is feasible and no feasible $q$ has a smaller objective; reason: this is attainment of the min of (2) at a constant vector
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 2, p.17, with (2), p.8

import Mathlib
import Definitions.Def_StaticProphetSec_UT
import Definitions.Def_StaticProphetSec_AR
import Definitions.Def_StaticProphetSec_pbE

namespace StaticProphetSec

/-- Lemma 2 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 2, p.17): for all `k, n` with `n > k` and all
`φ ∈ (0, 1)`, the problem `Φ_n(AR_k, UT_k, φ)` of (2), p.8, namely minimizing `E[AR_k(D_q)]` over
`q ∈ [0, 1]^n` subject to `E[UT_k(D_q)] = φ`, has an optimal solution in which all `q_i` are
equal. -/
theorem lemma_2 (k n : ℕ) (hk : 1 ≤ k) (hkn : k < n) (φ : ℝ) (hφ0 : 0 < φ) (hφ1 : φ < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ pbE (UT k) (fun _ : Fin n => r) = φ ∧
      ∀ q : Fin n → ℝ, (∀ i, 0 ≤ q i ∧ q i ≤ 1) → pbE (UT k) q = φ →
        pbE (AR k) (fun _ : Fin n => r) ≤ pbE (AR k) q := by sorry

end StaticProphetSec
