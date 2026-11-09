-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_3_2
-- name    : RankingQueryCost.Joint.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:39.604941+00:00
-- url     : https://prove2.me/theorems/a749611f-17a6-4922-a0fc-04a9508be66d
-- title:
--   Lemma 3.2 — Uniform control of faulty coefficients
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Fix a graph $E$ of at most $s$ identities and deterministic $0<p_e\le1$. Independently sample $I_e\sim\mathrm{Bernoulli}(p_e)$, put $w_e=I_e/p_e$, and $V_E=\sum_{e\in E}(1/p_e-1)$. For the Euclidean fluctuation $H_E$ defined above,
--
--   $$\mathbb EH_E\le4\sqrt{V_E},\qquad
--   \left\|\sum_{e\in E}w_ec_ex_e\right\|_2\le\sqrt U+H_E\quad\text{for every }|c_e|\le1.$$
--
--   The second inequality holds on every mask simultaneously for every coefficient vector, including history-dependent choices. The expectation and pointwise conclusions are separate clauses.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - encoding: expectation under the stated finite sampling law → the exact finite probability-weighted sum over all masks or independent priority permutations; reason: finite products give precisely the prescribed independent sampling distribution without integrability defaults
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 3.2, p. 7, PDF p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Flow

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 3.2, p. 7 / PDF 8. Finite product probabilities encode independent Bernoulli
variables exactly; coefficients in the second clause may be chosen after seeing the mask. -/
theorem lemma_3_2 (n s : ℕ) (hadm : Admissible n s)
    (E : Finset (Pair n)) (hE : E.card ≤ s)
    (p : Pair n → ℝ) (hp : ∀ e ∈ E, 0 < p e ∧ p e ≤ 1) :
    (∑ mask : (E → Bool),
      (∏ e : E, if mask e then p e else 1 - p e) *
        faultyFluctuation E (fun e => if he : e ∈ E then
          (if mask ⟨e, he⟩ then 1 / p e else 0) else 0)) ≤
      4 * Real.sqrt (∑ e ∈ E, (1 / p e - 1)) ∧
    (∀ mask : E → Bool, ∀ c : Pair n → ℝ, (∀ e ∈ E, |c e| ≤ 1) →
      euclideanNorm (flow E (fun e => if he : e ∈ E then
        (if mask ⟨e, he⟩ then 1 / p e else 0) * c e else 0)) ≤
      Real.sqrt (errorScale n s : ℝ) +
        faultyFluctuation E (fun e => if he : e ∈ E then
          (if mask ⟨e, he⟩ then 1 / p e else 0) else 0)) := by sorry

end RankingQueryCost.Joint
