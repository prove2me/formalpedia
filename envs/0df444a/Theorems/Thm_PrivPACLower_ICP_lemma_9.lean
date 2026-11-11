-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_9
-- name    : PrivPACLower.ICP.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:00.427634+00:00
-- url     : https://prove2.me/theorems/5961f05a-a373-480f-a640-97a1d0f5f16b
-- title:
--   Lemma 9 — repetition trades privacy for sample size
-- statement:
--   Let $0<\varepsilon\le0.1$, $0\le\delta<1$, $m\ge1$, and $\ell=\lfloor0.1/\varepsilon\rfloor$. Let $M$ be an $(\varepsilon,\delta)$-DP mechanism on $\ell m$ examples, and define $M'(S)=M(\operatorname{repeat}_\ell S)$. Then
--
--   $$M'\text{ is }(0.1,\delta/\varepsilon)\text{-DP}.$$
--
--   For every empirical error threshold $\gamma$ and failure bound $\eta$, if $M$ obeys those bounds on every realizable database of length $\ell m$, then $M'$ obeys the same bounds on every realizable database of length $m$ for the same nonempty class $H$. Repetition preserves each hypothesis's empirical error and realizability. This is the source of the inverse privacy factor in the goal.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: each of m examples repeated ell times → the product index Fin ell times Fin m, flattened by finProdFinEquiv; reason: lists one whole copy of the database per repetition; each original record occurs exactly ell times
--   - reading: M an (ε, δ)-DP mechanism on ℓm examples → M a mechanism whose outputs are hypotheses X → Bool (Learner X (ℓ*m)); reason: the empirical error and failure-probability guarantees the lemma transfers are defined only for hypothesis outputs
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 16, Lemma 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Reductions
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_9 {X : Type*} {m : ℕ} (hm : 1 ≤ m)
    (H : Set (X → Bool)) (hH : H.Nonempty) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1/10) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : Learner X (⌊(1/10 : ℝ)/ε⌋₊ * m)) (hpriv : IsDP M ε δ) :
    IsDP (repeatedLearner ⌊(1/10 : ℝ)/ε⌋₊ M) (1/10) (δ/ε) ∧
      ∀ γ η : ℝ, EmpiricalGuarantee H M γ η →
        EmpiricalGuarantee H (repeatedLearner ⌊(1/10 : ℝ)/ε⌋₊ M) γ η := by sorry

end PrivPACLower.ICP
