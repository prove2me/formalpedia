-- Prove2me | Theorems.Thm_Thm_1_2_4_tagsInPartition_concat
-- name    : Thm_1_2_4.tagsInPartition_concat
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:02:57.736815+00:00
-- url     : https://prove2.me/theorems/3e1fb143-d3ce-4741-8a75-32be01bf5e27
-- title:
--   Source theorem: Thm_1_2_4.tagsInPartition_concat
-- statement:
--   Exact source-backed Lean theorem Thm_1_2_4.tagsInPartition_concat from ProbabilityTheory.chapter_01.thm_1_2_4. The proposition and assumptions are preserved in the formal statement. The original proof remains in the pinned source project.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean#L998

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F003
import Mathlib.Tactic


/- The whole file thm_1_2_4.lean is devoted to the proof of Theorem 1.2 part 4

  High-level proof explanation for `rsIntegral_split`.

  This theorem proves the additivity of the Riemann--Stieltjes integral over adjacent
  intervals:

      ∫_a^b f dα = ∫_a^c f dα + ∫_c^b f dα,

  assuming `a < c < b` and integrability on `[a,b]`.

  Mathematically, the proof is standard: split a sufficiently fine partition of
  `[a,b]` at the intermediate point `c`, compare the corresponding upper/lower
  sums on `[a,b]`, `[a,c]`, and `[c,b]`, and then use uniqueness of the limiting
  integral value.

  The reason the Lean proof is long is not that the analytic idea is complicated.
  The analytic content is essentially just:

      upper/lower sums over `[a,b]`
        = upper/lower sums over `[a,c]`
          + upper/lower sums over `[c,b]`

  for partitions containing `c`, followed by an ε-argument.

  The real difficulty is finite partition bookkeeping.  In Lean, partitions are
  indexed by finite types such as `Fin (P.n + 1)` for points and `Fin P.n` for
  subintervals.  Splitting or merging partitions therefore requires explicit
  constructions and proofs that are usually suppressed on paper:

  * constructing partitions of `[a,c]` and `[c,b]` from a partition of `[a,b]`
    containing `c`;
  * constructing a partition of `[a,b]` by concatenating partitions of `[a,c]`
    and `[c,b]`;
  * proving that the endpoint `c` occurs at the correct index;
  * proving that the subintervals before `c` and after `c` correspond to the
    expected subintervals of the original partition;
  * proving that the sums over the original partition decompose into the two
    sums over the left and right partitions;
  * proving that the `α`-increments and the `lowerStep`/`upperStep` terms are
    preserved under these index identifications;
  * handling the inevitable coercions between different finite index types.

  In an informal proof, all of this is hidden in phrases like “split the partition
  at `c`” or “combine the two partitions.”  Lean requires each of these operations
  to be represented by an explicit map between finite index types, together with
  proofs that the maps preserve the relevant points, intervals, and sums.

  Thus the proof is long mainly because it formalizes the finite ordered
  combinatorics of partitions, not because the underlying analysis is subtle.
  Once the partition-splitting and sum-decomposition lemmas are established, the
  final analytic argument is a routine squeeze/uniqueness argument using the
  already-proved upper/lower or tagged-sum characterization of the integral.

  Future readers who only need the theorem may safely treat the body of this proof
  as partition-index infrastructure plus the standard interval-additivity argument.
-/

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

-----------------------------------------------------------------------------
-- 1. Analytical Helper Lemmas
-----------------------------------------------------------------------------

noncomputable section SubintervalIntegrability

-----------------------------------------------------------------------------
-- 1. Constructing the Exact Value (Darboux Supremum)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 2. Partition Surgery
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 3. The Cauchy Squeeze Lemma
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 4. Limits Converging to the Darboux Supremum
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- Helper Lemmas: Tagged Sums are Squeezed by Upper and Lower Sums
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- The Squeeze Theorem Application
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 5. Main Existence Theorem
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- 6. The Right Subinterval Limits and Existence (Symmetric to Left)
-----------------------------------------------------------------------------

end SubintervalIntegrability

/-
The core limit additivity: If the tagged sums converge to L₁ on [a, c]
and to L₂ on [c, b], then their combined partition sums converge to L₁ + L₂
on the whole interval [a, b].
(This requires the partition surgery bound: |S(P) - S(P ∪ {c})| < ε).
-/
-- theorem taggedCommonLimit_split {f α : ℝ → ℝ} {a c b L₁ L₂ : ℝ}
--     (hac : a < c) (hcb : c < b)
--     (h₁ : TaggedCommonLimit a c f α L₁)
--     (h₂ : TaggedCommonLimit c b f α L₂) :
--     TaggedCommonLimit a b f α (L₁ + L₂) := sorry

theorem tagsInPartition_concat {a c b : ℝ} {P1 : Partition a c} {P2 : Partition c b}
    {tags1 : Fin P1.n → ℝ} {tags2 : Fin P2.n → ℝ}
    (ht1 : tagsInPartition P1 tags1) (ht2 : tagsInPartition P2 tags2) :
    tagsInPartition (concatPartition P1 P2) (concatTags tags1 tags2) := by sorry

-----------------------------------------------------------------------------
--  The Main Theorem: Integral Splitting
-----------------------------------------------------------------------------

end Thm_1_2_4 -- namespace

end Thm_1_2_4  -- section
