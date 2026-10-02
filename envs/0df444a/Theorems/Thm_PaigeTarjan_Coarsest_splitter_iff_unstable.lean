-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_splitter_iff_unstable
-- name    : PaigeTarjan.Coarsest.splitter_iff_unstable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:46:59.63855+00:00
-- url     : https://prove2.me/theorems/9ec264d4-8572-4475-9425-1b1bcc0a97ed
-- title:
--   §3, p. 978 — S is a splitter of Q iff Q is unstable with respect to S
-- statement:
--   Let $E$ be a relation on a finite set $U$, let $Q$ be a partition of $U$ and let $S \subseteq U$. Recall that $S$ is a **splitter** of $Q$ if $\mathrm{split}(S,Q) \neq Q$. Then
--   $$\mathrm{split}(S, Q) \neq Q \iff Q \text{ is not stable with respect to } S.$$
--
--   Equivalently, refining a partition by a set leaves it unchanged exactly when the partition is already stable with respect to that set. This is the test the refinement algorithms use to decide whether a set can still be used for refinement.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 978, §3, paragraph defining split(S, Q), last sentence

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

namespace PaigeTarjan.Coarsest

/-- §3, p. 978: for a partition `Q` of `U` and a set `S ⊆ U`, `S` is a splitter of `Q`
(`split(S, Q) ≠ Q`) if and only if `Q` is unstable with respect to `S`. -/
theorem splitter_iff_unstable {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S : Finset U)
    (hQ : IsPartition Q) :
    split E S Q ≠ Q ↔ ¬ StableWrt E Q S := by sorry

end PaigeTarjan.Coarsest
