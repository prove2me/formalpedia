-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_21
-- name    : PrivPACLower.ICP.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:13.516477+00:00
-- url     : https://prove2.me/theorems/2679517d-fae4-44d1-bb58-d1ac7ec0d6c1
-- title:
--   Lemma 21 — exponential mechanism privacy, tail and expectation
-- statement:
--   Let $C$ be a nonempty finite candidate set, let $\varepsilon>0$, and let $\Delta>0$ bound the absolute change of $s(D,c)$ under replacement of one database record, uniformly in $c$. Normalize weights $\exp(\varepsilon s(D,c)/(2\Delta))$ to obtain $A(D)$. Then $A$ is a probability mechanism and is $(\varepsilon,0)$-DP. Writing $\mathrm{OPT}(D)=\max_{c\in C}s(D,c)$, for every $t>0$,
--
--   $$\Pr\!\left[s(D,A(D))\le\mathrm{OPT}(D)-\frac{2\Delta}{\varepsilon}(\ln|C|+t)\right]\le e^{-t},$$
--
--   and
--
--   $$\mathbb E[s(D,A(D))]\ge\mathrm{OPT}(D)-\frac{2\Delta}{\varepsilon}(\ln|C|+1).$$
--
--   All three guarantees belong to this item. The utility bounds supply the private selection statement.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: finite nonempty candidate space and positive score sensitivity → Fintype and Nonempty candidate space with measurable singletons and sensitivity greater than zero; reason: makes normalization, maximum and division well-defined; finite measurable singleton spaces have every subset measurable
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 37, Lemma 21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Exponential
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_21 {Z C : Type*} [Fintype C] [Nonempty C]
    [MeasurableSpace C] [MeasurableSingletonClass C] {n : ℕ}
    (score : (Fin n → Z) → C → ℝ) (ε sensitivity : ℝ)
    (hε : 0 < ε) (hs : 0 < sensitivity)
    (hscore : ∀ D D', Neighbors D D' → ∀ c, |score D c - score D' c| ≤ sensitivity) :
    ∃ A : Mechanism Z C n,
      (∀ D, (A D : Measure C) = exponentialLaw score ε sensitivity D) ∧
      IsDP A ε 0 ∧
      (∀ D (t : ℝ), 0 < t →
        (A D : Measure C) {c | score D c ≤ optimum score D -
          (2*sensitivity/ε)*(Real.log (Fintype.card C : ℝ)+t)} ≤
            ENNReal.ofReal (Real.exp (-t))) ∧
      (∀ D, optimum score D - (2*sensitivity/ε)*(Real.log (Fintype.card C : ℝ)+1) ≤
        ∫ c, score D c ∂(A D : Measure C)) := by sorry

end PrivPACLower.ICP
