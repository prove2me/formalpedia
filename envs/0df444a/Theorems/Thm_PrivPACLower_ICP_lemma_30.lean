-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_30
-- name    : PrivPACLower.ICP.lemma_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:00.975526+00:00
-- url     : https://prove2.me/theorems/35e186bd-ccd1-47e8-b20b-135c72edf055
-- title:
--   Lemma 30 — the strict baseline private learner lower bound
-- statement:
--   Let $H$ be non-trivial: there are two members agreeing at one domain point and disagreeing at another. Suppose $\varepsilon>0$, $0\le\delta\le\varepsilon$, $0<\alpha\le1/4$, and $0<\beta\le1/3$. Every possibly improper $(\varepsilon,\delta)$-DP, $(\alpha,\beta)$-PAC learner for $H$ on $n$ examples satisfies
--
--   $$n>\frac1{288\alpha\varepsilon}.$$
--
--   The inequality is strict. This supplies the baseline cost needed even when a packing has only one inexpensive component.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - generalization: PAC for every realizable distribution and privacy for every output event → PAC for all realizable PMFs and privacy for product-measurable events of arbitrary probability-measure outputs; reason: weakens learner hypotheses on arbitrary domains; every source learner satisfies them, and finite component domains retain all laws and events
--   - generalization: 0 ≤ δ ≤ ε, with δ ∈ [0,1) from the DP definition on p. 10 → 0 ≤ δ ≤ ε with no upper bound δ < 1; reason: the proof on p. 43 never uses δ < 1 (for δ ≥ 1 privacy is vacuous and the bound still holds); on δ < 1 it is the printed lemma
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 43, Lemma 30. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_30 {X : Type*} {n : ℕ} (H : Set (X → Bool))
    (hH : NontrivialClass H) (ε δ α β : ℝ) (hε : 0 < ε)
    (hδ : 0 ≤ δ ∧ δ ≤ ε) (hα : 0 < α ∧ α ≤ 1/4)
    (hβ : 0 < β ∧ β ≤ 1/3) (M : Learner X n)
    (hpriv : IsDP M ε δ) (hpac : IsPACLearner H M α β) :
    (n : ℝ) > 1/(288*α*ε) := by sorry

end PrivPACLower.ICP
