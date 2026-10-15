-- Prove2me | Theorems.Thm_SecretaryAdvice_Samples_best_so_far_reduction
-- name    : SecretaryAdvice.Samples.best_so_far_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:41:53.965508+00:00
-- url     : https://prove2.me/theorems/811b6199-ad5b-48e5-819b-002c207a7517
-- title:
--   §2, p. 6 — without loss of optimality a policy stops only at best-so-far secretaries (samples model)
-- statement:
--   In the secretary problem with $k$ samples and $n$ secretaries, for every policy $q$ (stopping probabilities in $[0,1]$ that depend only on the information) there is a policy $q'$ that stops only in rounds where the current secretary is the best so far, i.e. $q'_i(x)=0$ whenever $T_i$ fails on $x$, and
--   $$\mathrm{win}(q)\le\mathrm{win}(q').$$
--
--   This is the remark of §2 that "one can assume without loss of optimality that the algorithm only picks secretary $i$ if it is the best-so-far". It brings any policy into the form assumed by Proposition 9.
--
--   **Formalization Note** "Best so far" is read off the information by `infoBestSoFar`, which compares the current secretary with the earlier secretaries (not with the samples).
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 6, §2 Best-so-far Event (remark after eq. (1))

import Mathlib
import Definitions.Def_SecretaryAdvice_Samples_Setting

namespace SecretaryAdvice.Samples

theorem best_so_far_reduction (n k : ℕ) (q : Policy n k) (hq : ValidPolicy q) :
    ∃ q' : Policy n k, ValidPolicy q' ∧
      (∀ (i : Fin n) (x : Info k i.val), infoBestSoFar x = false → q' i x = 0) ∧
      win q ≤ win q' := by sorry

end SecretaryAdvice.Samples
