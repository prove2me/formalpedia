-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_Supplement_theorem_B_3
-- name    : SublinearChoresMMS.Disposal.Supplement.theorem_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:48.433726+00:00
-- url     : https://prove2.me/theorems/bf78dc23-a1d2-42af-9a1e-9b663a661af3
-- title:
--   Theorem B.3 — PROP and ordinal MMS with sublinear deficit
-- statement:
--   Put $f(n)=n^{2/3}(\log(2n))^{2/3}$. There exist an absolute $C>0$ and an integer function $d(n)$, both chosen before all cost profiles, such that for every $n\ge1$,
--
--   $$1\le d(n)\le n,\qquad n-d(n)\le C f(n).$$
--
--   Every finite nonnegative real additive-chores instance then has one finite law of complete allocations satisfying
--
--   $$\mathbb E[c_i(X_i)]\le\frac{c_i(M)}n\quad(i\in[n]),\qquad c_i(X_i)\le\operatorname{MMS}^{d(n)}_i(M)$$
--
--   for every agent in every positive-weight outcome. The second benchmark is the cost minimax over all $d(n)$-partitions of the original full chore set. Proportionality continues to use denominator $n$. Zero costs, zero benchmarks, ties, empty chores and $n=1$ are included; bounded $n$ may use $d=1$. This is an ordinal guarantee for every agent, rather than a bound on the number of exceptions.
--
--   Differences from the source:
--   - reading: the tilde-O n^(2/3) bound in the short Appendix B theorem → one absolute C multiplying n^(2/3)*(log(2*n))^(2/3), before all instance data; reason: equation (3), printed 31 / PDF 32, supplies this logarithmic power with a constant independent of k; log(2n) and enlarging C include bounded positive n
--   - encoding: d=n minus tilde-O n^(2/3) → one integer function d(n) chosen before all cost profiles, with 1≤d(n)≤n and n-d(n)≤C*f(n); reason: the proof chooses k from the instance-independent residual bound (3); bounded n may use d=1 and the PROP denominator remains n
--   - encoding: finite agents, chores, complete partitions and finite lotteries → zero-based Fin labels, owner maps and published finite real-weight laws with positive-weight support; reason: bijections cover exactly the finite source instances, and repeated lottery atoms can be merged
--   - encoding: cost minimax share over all positive-part-count labelled partitions → the published costShare, the negative of the goods maximin functional on negative additive costs; reason: finite sign duality gives the same attained minimax without imposing any goods nonnegativity predicate
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Theorem B.3, printed p. 32 / PDF p. 33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf Rate evidence: equation (3), printed p. 31 / PDF p. 32.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_AppendixPacking

namespace SublinearChoresMMS.Disposal.Supplement

/-- Theorem B.3, printed 32 / PDF 33; (3) fixes the rate independently of k.
d is chosen before every cost profile, and PROP still uses n. -/
theorem theorem_B_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ → ℕ,
      ∀ n : ℕ, 0 < n →
        (1 ≤ d n ∧ d n ≤ n ∧ ((n - d n : ℕ) : ℝ) ≤ C * appendixRate n) ∧
        ∀ (m : ℕ) (c : Cost n m), Nonnegative c →
          ∃ P : FiniteLaw (Allocation n m),
            (∀ i, P.mean (fun X => cost c i (bundle X i)) ≤ propShare c i) ∧
            ∀ a, 0 < P.weight a → ∀ i,
              cost c i (bundle (P.atom a) i) ≤ costShare (c i) (d n) := by sorry

end SublinearChoresMMS.Disposal.Supplement
