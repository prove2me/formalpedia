-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_1
-- name    : SublinearChoresMMS.Disposal.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:32:12.506165+00:00
-- url     : https://prove2.me/theorems/02823d71-1292-48ef-8f70-fce40a51dfef
-- title:
--   Lemma 3.1 — representative packing, with the segment conclusion of Appendix A.1.3
-- statement:
--   There are absolute positive constants $A,B$ and a universal threshold $n_0$ such that the following holds. Take $n\ge n_0$, the section's $q=2^{\lfloor\log_2\sqrt{n\log n}\rfloor}$, and $m\ge q$ divisible by $q$. In the normalized positive distinct IDO regime, for each agent there is a bin or exclusion label for every representative except the first such that
--
--   $$\#\text{excluded representatives}\le A\sqrt L,\qquad\#\text{constant segments}\le BL^3,$$
--
--   where $L=\lfloor n/q\rfloor$ and $h=n\bmod q$. All retained representatives are partitioned among $L$ bins of cost at most one and, exactly when $h>0$, one additional bin of cost at most $h/q$. Both the partition and exclusions may depend on the agent. Segment labels include exclusions and refer to consecutive representatives in the common order, independently of $m$.
--
--   This retains the packing statement and the segment control established for the same output in Appendix A.1.3.
--
--   Differences from the source:
--   - generalization: the short Lemma 3.1 statement asserts the capacity and exclusion bounds → the same packing additionally has at most B*L^3 constant bin-or-exclusion segments; reason: Appendix A.1.3 Step 5 proves this extra conclusion and Section 3.2 needs it to control the number of profiles
--   - encoding: finite agents, chores, complete partitions and finite lotteries → agents Fin n, chores Fin m, allocation maps and normalized finite lists with real weights; reason: bijections identify the same finite instances and partitions; repeated lottery atoms may be merged and positive weights define support
--   - encoding: cost minimax share over labelled partitions → the negative of LittleCharity.MMS.mms evaluated at negative additive bundle costs; reason: negation exchanges finite maxima and minima; no goods nonnegativity predicate is imposed, and costShare_spec states the attained minimax characterization
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 3.1, printed p. 6 / PDF p. 7; standing regime §2 and §3; Appendix A.1.3 Step 5, printed p. 26 / PDF p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Lemma 3.1, printed p. 6 / PDF p. 7, including the segment property established
in Appendix A.1.3, printed pp. 24–26 / PDF pp. 25–27. The last bin remains fractional. -/
theorem lemma_3_1 :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
        blockSize n ≤ m → blockSize n ∣ m →
        ∀ c : Cost n m, Normalized c → ∀ i : Fin n,
          ∃ p : Labels n m (blockSize n), ValidPacking c i p ∧
            (excludedCount p : ℝ) ≤ A * Real.sqrt (n / blockSize n : ℕ) ∧
            (segments p : ℝ) ≤ B * (n / blockSize n : ℕ) ^ 3 := by sorry

end SublinearChoresMMS.Disposal
