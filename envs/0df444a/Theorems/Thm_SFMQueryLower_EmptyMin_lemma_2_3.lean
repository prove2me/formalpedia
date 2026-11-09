-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_lemma_2_3
-- name    : SFMQueryLower.EmptyMin.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:18.841006+00:00
-- url     : https://prove2.me/theorems/8fedb212-b1ee-4e83-a25e-b218c29db297
-- title:
--   Lemma 2.3 — all properties of the hard family
-- statement:
--   Let $n\ge2$, let $\Pi=(P_1,R_1,\ldots,P_k,R_k)$ be an ordered partition into nonempty blocks, and let $P^\star=\bigcup_iP_i$. The explicitly constructed functions of Definition 2.2 satisfy all three conclusions:
--
--   1. Both $f_0^\Pi$ and $f_1^\Pi$ are submodular.
--   2. For either bit $b$, $f_b^\Pi(P^\star)=b-1$, and $f_0^\Pi(S)=f_1^\Pi(S)$ whenever $S\ne P^\star$.
--   3. For either bit,
--   $$f_b^\Pi(\varnothing)=0,\qquad \min_{S\subseteq[n]}f_b^\Pi(S)=b-1,\qquad \operatorname{EmptyMin}(f_b^\Pi)\iff b=1.$$
--
--   This establishes that the hard family is a valid input family and that its two answers can be distinguished at exactly one set. The minimum includes attainment.
--
--   **Formalization Note** The construction uses integer arithmetic before the real-valued embedding. The minimum is expressed by a least element of the range.
--
--   Differences from the source:
--   - encoding: finite labeled ground sets and their subsets → Fin n and Finset (Fin n); reason: bijections relabel every finite source instance
--   - encoding: layers indexed from 1 and bits in {0,1} → blocks indexed by Fin k with Boolean slots, and Bool hidden bits; reason: source index j+1 corresponds to stored index j and false/true to 0/1
--   - encoding: the attained minimum equals b-1 → IsLeast of the function range at the embedded integer b-1; reason: includes the exact lower bound and attainment without totalized real infima
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma 2.3, printed p. 8 / PDF p. 9; proof Appendix A.2, printed pp. 14–15 / PDF pp. 15–16

import Definitions.Def_SFMQueryLower_EmptyMin_EmptyMinProblem
import Definitions.Def_SFMQueryLower_EmptyMin_HardFamily

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Fox, Lemma 2.3, printed p.8 / PDF p.9; proof Appendix A.2, pp.14–15.
All three clauses are retained. `false/true` encode bits `0/1`; `IsLeast` includes
attainment of the minimum, without using a totalized real infimum. -/
theorem lemma_2_3 (n k : ℕ) (hn : 2 ≤ n) (π : OrderedPartition n k) :
    (∀ b : Bool, NonmonotoneSubmod.Shared.Submodular (hardFunction π b)) ∧
    (∀ b : Bool, hardFunction π b (distinguishedSet π) =
      (if b then (1 : ℝ) else 0) - 1) ∧
    (∀ S : Finset (Fin n), S ≠ distinguishedSet π →
      hardFunction π false S = hardFunction π true S) ∧
    (∀ b : Bool, hardFunction π b ∅ = 0 ∧
      IsLeast (Set.range (hardFunction π b)) ((if b then (1 : ℝ) else 0) - 1) ∧
      (EmptyMinimizes (hardFunction π b) ↔ b = true)) := by sorry

end SFMQueryLower.EmptyMin
