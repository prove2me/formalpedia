-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_9
-- name    : SwitchingStable.Universal.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:35.170454+00:00
-- url     : https://prove2.me/theorems/58a95732-d3ee-4765-9517-3938197c4850
-- title:
--   Lemma 9 — Nested swap maps and unique predecessors
-- statement:
--   In the promoted market the first-swap map sends $W$ injectively into $E\setminus E_{\rm adj}$. Both the one-swap map on $E\setminus E_{\rm adj}$ and the two-swap map on $W$ are injective. With $b_E,b_W$ counting source occurrences whose prescribed images lie outside $T_0$,
--   $$w\le e-e_{\rm adj},\qquad b_W\le b_E\le r_0-t_0.$$
--   There are exactly $e-e_{\rm adj}-b_E$ eligible one-swap predecessors and $w-b_W$ eligible two-swap predecessors of tails. The displayed injectivity gives at most one of each for every fixed tail occurrence.
--
--   Differences from the source:
--   - encoding: Eligible predecessor counts and uniqueness under the prescribed swaps → Injectivity on the full occurrence domains, with exact finite counts of sources whose images are tails; reason: An injective map into tails has at most one predecessor of its kind at each tail; sources, not arbitrary image partitions, define the counts.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 6, PDF p. 7, Lemma 9

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_9 {n : ℕ} (I : StableMatching.Instance n) (hI : StablePartnersFirst I) (ε : Direction) :
    (∀ (μ : StableMatching.Matching n) (u : Fin n), I.IsStable μ → W I μ ε u →
      I.IsStable (swap I μ ε u) ∧ E I (swap I μ ε u) ε u ∧ ¬ Eadj I (swap I μ ε u) ε u) ∧
    (∀ (μ : StableMatching.Matching n) (u : Fin n), I.IsStable μ → E I μ ε u → ¬ Eadj I μ ε u →
      I.IsStable (swap I μ ε u) ∧ R0 I (swap I μ ε u) ε u) ∧
    (∀ (μ : StableMatching.Matching n) (u : Fin n), I.IsStable μ → W I μ ε u →
      I.IsStable (swapTwice I μ ε u) ∧ R0 I (swapTwice I μ ε u) ε u) ∧
    Set.InjOn (fun o : StableMatching.Matching n × Fin n => (swap I o.1 ε o.2, o.2))
      {o | I.IsStable o.1 ∧ W I o.1 ε o.2} ∧
    Set.InjOn (fun o : StableMatching.Matching n × Fin n => (swap I o.1 ε o.2, o.2))
      {o | I.IsStable o.1 ∧ E I o.1 ε o.2 ∧ ¬ Eadj I o.1 ε o.2} ∧
    Set.InjOn (fun o : StableMatching.Matching n × Fin n => (swapTwice I o.1 ε o.2, o.2))
      {o | I.IsStable o.1 ∧ W I o.1 ε o.2} ∧
    (let v := occurrenceCounts I ε
     v.w ≤ v.e-v.eadj ∧ v.bW ≤ v.bE ∧ v.bE ≤ v.r0-v.t0 ∧
     (count I (fun μ u => E I μ ε u ∧ ¬ Eadj I μ ε u ∧ T0 I (swap I μ ε u) ε u) : ℝ) = v.e-v.eadj-v.bE ∧
     (count I (fun μ u => W I μ ε u ∧ T0 I (swapTwice I μ ε u) ε u) : ℝ) = v.w-v.bW) := by sorry

end SwitchingStable.Universal
