-- Prove2me | Theorems.Thm_StaticProphetSec_lemma_7
-- name    : StaticProphetSec.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:21.511442+00:00
-- url     : https://prove2.me/theorems/a547dfea-604b-4147-a0af-100e8295e30c
-- title:
--   Lemma 7 — (17) and $\mathbb E[\mathrm{UT}_k(\mathrm{Pois}(k))]=\mathbb E[\mathrm{AR}_k(\mathrm{Pois}(k))]=\gamma_k$
-- statement:
--   For any $k\ge1$ and $\lambda\ge0$,
--
--   $$k\,\mathbb E[\mathrm{UT}_k(\mathrm{Pois}(\lambda))]=\lambda\,\mathbb P(\mathrm{Pois}(\lambda)<k)+k\,\mathbb P(\mathrm{Pois}(\lambda)>k)=\lambda\,\mathbb E[\mathrm{AR}_k(\mathrm{Pois}(\lambda))].$$
--
--   Therefore
--
--   $$\mathbb E[\mathrm{UT}_k(\mathrm{Pois}(k))]=\mathbb E[\mathrm{AR}_k(\mathrm{Pois}(k))]=\gamma_k.$$
--
--   So the Poisson limit is exactly where the two risks of Lemma 1 balance at $\gamma_k$.
--
--   Differences from the source:
--
--   - encoding: $\mathbb P(\mathrm{Pois}(\lambda)<k)$ and $\mathbb P(\mathrm{Pois}(\lambda)>k)$ → expectations of the indicator functions; reason: a probability is the expectation of an indicator
-- source:
--   Arnosti & Ma, Tight Guarantees for Static Threshold Policies in the Prophet Secretary Problem, arXiv:2108.12893v2, Lemma 7, p.29

import Mathlib
import Definitions.Def_StaticProphetSec_gamma
import Definitions.Def_StaticProphetSec_UT
import Definitions.Def_StaticProphetSec_AR
import Definitions.Def_StaticProphetSec_poisE

open scoped NNReal

namespace StaticProphetSec

/-- Lemma 7 (Arnosti & Ma, arXiv:2108.12893v2, Lemma 7, p.29): for `k ≥ 1` and `λ ≥ 0`,
`k E[UT_k(Pois(λ))] = λ P(Pois(λ) < k) + k P(Pois(λ) > k) = λ E[AR_k(Pois(λ))]`, equation (17);
and `E[UT_k(Pois(k))] = E[AR_k(Pois(k))] = γ_k`, equation (18). -/
theorem lemma_7 (k : ℕ) (hk : 1 ≤ k) :
    (∀ lam : ℝ≥0,
      (k : ℝ) * poisE (UT k) lam =
          (lam : ℝ) * poisE (fun j => if j < k then 1 else 0) lam
            + (k : ℝ) * poisE (fun j => if k < j then 1 else 0) lam ∧
      (lam : ℝ) * poisE (fun j => if j < k then 1 else 0) lam
          + (k : ℝ) * poisE (fun j => if k < j then 1 else 0) lam =
        (lam : ℝ) * poisE (AR k) lam) ∧
    poisE (UT k) (k : ℝ≥0) = gamma k ∧
    poisE (AR k) (k : ℝ≥0) = gamma k := by sorry

end StaticProphetSec
