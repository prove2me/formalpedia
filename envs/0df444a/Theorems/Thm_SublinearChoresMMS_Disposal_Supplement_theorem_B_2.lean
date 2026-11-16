-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_theorem_B_2
-- name    : SublinearChoresMMS.Disposal.Supplement.theorem_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:24.882125+00:00
-- url     : https://prove2.me/theorems/20da873b-451d-4528-ae28-1c6fa3351bfb
-- title:
--   Theorem B.2 — PROP and a uniform possible MMS exception
-- statement:
--   Put $f(n)=n^{2/3}(\log(2n))^{2/3}$. There exists an absolute $C>0$ such that every finite nonnegative real additive-chores instance with $n\ge1$ has a finite joint law of a complete allocation $X$ and a designated agent $J$. The same law satisfies
--
--   $$\Pr[J=i]=\frac1n,\qquad\mathbb E[c_i(X_i)]\le\frac{c_i(M)}n\quad(i\in[n]).$$
--
--   In every positive-weight outcome,
--
--   $$c_i(X_i)\le\mu_i\quad(i\ne J),\qquad c_i(X_i)\le C f(n)\mu_i\quad(i\in[n]).$$
--
--   The original $n$-part shares are used. The designated agent need not actually fail MMS. In particular each fixed agent meets MMS with probability at least $1-1/n$. All-zero rows, zero MMS, ties, $n=1$ and empty chores remain included. This companion theorem combines ex-ante fairness with at most one possible MMS exception in each outcome.
--
--   Differences from the source:
--   - reading: the tilde-O n^(2/3) bound in the short Appendix B theorem → one absolute C multiplying n^(2/3)*(log(2*n))^(2/3), before all instance data; reason: equation (3), printed 31 / PDF 32, supplies this logarithmic power with a constant independent of k; log(2n) and enlarging C include bounded positive n
--   - encoding: the non-MMS agent is chosen uniformly → a finite joint law (X,J) with Pr[J=i]=1/n and exact MMS for every i≠J in each supported outcome; reason: J is the uniformly designated possible exception, including outcomes where nobody fails MMS; no conditional-on-failure assertion is introduced
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
--   - encoding: cost minimax share over all positive-part-count labelled partitions → the published costShare, the negative of the goods maximin functional on negative additive costs; reason: finite sign duality gives the same attained minimax without imposing any goods nonnegativity predicate
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Theorem B.2, printed p. 31 / PDF p. 32. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf Rate evidence: equation (3), printed p. 31 / PDF p. 32.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_AppendixPacking

noncomputable section

namespace SublinearChoresMMS.Disposal.Supplement

attribute [local instance] Classical.propDecidable

/-- Theorem B.2, printed 31 / PDF 32, resolving the suppressed logarithms by (3).
J is uniformly designated; it is not required actually to violate MMS. -/
theorem theorem_B_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ (m : ℕ) (c : Cost n m),
      Nonnegative c → ∃ P : FiniteLaw (Allocation n m × Fin n),
        (∀ i, P.mean (fun o => if o.2 = i then 1 else 0) = 1 / (n : ℝ)) ∧
        (∀ i, P.mean (fun o => cost c i (bundle o.1 i)) ≤ propShare c i) ∧
        ∀ a, 0 < P.weight a → ∀ i,
          (i ≠ (P.atom a).2 → cost c i (bundle (P.atom a).1 i) ≤ mu c i) ∧
          cost c i (bundle (P.atom a).1 i) ≤ C * appendixRate n * mu c i := by sorry

end SublinearChoresMMS.Disposal.Supplement
