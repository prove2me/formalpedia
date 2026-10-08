-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_picked_before_iff_index_ge
-- name    : TsitsiklisGittins.IndexTheorem.picked_before_iff_index_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:21.589987+00:00
-- url     : https://prove2.me/theorems/a8aa2a6f-8dd6-4263-a495-e778d3c2e857
-- title:
--   A state x can be picked before y by the index algorithm if and only if γ(x) ≥ γ(y)
-- statement:
--   Consider the semi-Markov multi-armed bandit problem with finite nonempty state spaces, and let $\gamma$ be the indices produced by a run of the index algorithm. For distinct states $x,y\in\mathcal X$,
--   $$
--   \gamma(x)\ge\gamma(y)\iff x\ \text{is picked before}\ y\ \text{in some run of the index algorithm that yields the same indices}\ \gamma .
--   $$
--
--   "Can be picked" refers to the freedom in step (a) of the algorithm when several states attain the maximal rate. Combined with the optimality of the picking orders, it shows that every priority order compatible with the indices is optimal (Theorem 2.2).
--
--   **Formalization Note** The runs on the right-hand side are required to produce the same index function $\gamma$ on all of $\mathcal X$, which is the reading under which the claim yields Theorem 2.2; ties in $\gamma$ are allowed.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 198 (PDF p. 5), Section 2, proof of Theorem 2.2, second sentence

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_IndexRun

namespace TsitsiklisGittins.IndexTheorem

/-- Proof of Theorem 2.2 of Tsitsiklis (1994), p. 198: given the indices `γ` of a run of the index
algorithm, a state `x` can be picked before a state `y` by the index algorithm (in some run that
yields the same indices `γ`) if and only if `γ(x) ≥ γ(y)`. -/
theorem picked_before_iff_index_ge {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (seq : List (Σ i, X i)) (γ : (Σ i, X i) → ℝ) (hrun : B.IsIndexRun seq γ)
    (x y : Σ i, X i) (hxy : x ≠ y) :
    γ y ≤ γ x ↔ ∃ seq' : List (Σ i, X i), B.IsIndexRun seq' γ ∧ seq'.idxOf x < seq'.idxOf y := by sorry

end TsitsiklisGittins.IndexTheorem
