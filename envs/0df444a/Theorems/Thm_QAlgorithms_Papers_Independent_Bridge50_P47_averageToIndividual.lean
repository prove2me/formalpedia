-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_averageToIndividual
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.averageToIndividual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:49:49.736483+00:00
-- url     : https://prove2.me/theorems/201d4ade-9407-4a07-bc40-16111010c0dc
-- title:
--   Section VI: converting averaged privacy/error to individual criteria
-- statement:
--   Fix $\varepsilon,\delta,a>0$. There exists $C\ge0$, depending only on these three numbers, such that the following holds uniformly over all nonzero finite input, output and environment dimensions, all Stinespring isometries $U$, all $n\ge1$, and all private codes with averaged purified error at most $\varepsilon$ and averaged purified privacy at most $\delta$. There is a new valid code whose signal states are probability mixtures of the original signal states, with $M'$ messages, such that
--
--   $$
--   \log_2 M'\ge\log_2 M-C,\qquad
--   \varepsilon'_m<(1+a)\varepsilon,\qquad
--   \delta'_m<(1+a)\delta\quad\text{for every message }m.
--   $$
--
--   Here $\varepsilon'_m$ is the purified error of decoding message $m$. There is one normalized environment state $\sigma$ for which $\delta'_m=P(\mathcal N^{c\otimes n}(\rho'_m),\sigma)$ satisfies the displayed bound for every message. Randomized encoding upgrades both averaged criteria with constant information loss, also allowing a one-message code for small message sets.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 9, Section VI: converting averaged privacy/error to individual criteria

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Section VI long Remark, PDF pp.8–9: qualitative constant information
loss. The constant precedes channel, code and n; encoding is an actual mixture
of old signal states, with one privacy witness for all messages. -/
theorem averageToIndividual (epsilon delta a : ℝ)
    (he : 0 < epsilon) (hd : 0 < delta) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ b e d : ℕ, 0 < b → 0 < e → 0 < d →
    ∀ U : Matrix (Fin e × Fin d) (Fin b) ℂ, P67.IsIsometry U →
    ∀ n : ℕ, 1 ≤ n → ∀ code : P67.PrivateCode (Fin b) (Fin e) n,
      PrivateGood U code epsilon delta →
      ∃ newCode : P67.PrivateCode (Fin b) (Fin e) n,
        RandomizedFrom code newCode ∧
        IndividualGood U newCode ((1 + a) * epsilon) ((1 + a) * delta) ∧
        Real.logb 2 code.M - C ≤ Real.logb 2 newCode.M := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
