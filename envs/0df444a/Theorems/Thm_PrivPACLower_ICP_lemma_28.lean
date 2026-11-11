-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_28
-- name    : PrivPACLower.ICP.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:00.560191+00:00
-- url     : https://prove2.me/theorems/ef6e8b32-1549-4960-95d8-2a0eb1025e26
-- title:
--   Lemma 28 — private expected empirical error controls population error
-- statement:
--   Let $q\ge1$, $\varepsilon>0$, $0\le\delta<1$, and let $M$ be an $(\varepsilon,\delta)$-DP algorithm on $q$ labeled examples whose output is an arbitrary binary hypothesis. For every labeled-example PMF $\mu$,
--
--   $$\mathbb E_{S\sim\mu^q,M}[\operatorname{err}_\mu(M(S))]\le e^\varepsilon\mathbb E_{S\sim\mu^q,M}[\operatorname{err}_S(M(S))]+\delta.$$
--
--   Both expectations average jointly over the sample and the learner output. Realizability is unnecessary. This is the expected-error comparison used by the hard-distribution lemma.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - reading: a distribution on a bare set with no sigma-algebra specified → a PMF, allowing arbitrary countable support; reason: uses the brief's discrete-law interpretation; on every finite domain this includes all distributions
--   - generalization: M (ε, δ)-DP for every output event → M (ε, δ)-DP for product-measurable events of X → Bool; reason: weaker privacy hypothesis; the proof on p. 42 uses only the cylinder events {h : h(x) ≠ b}, and every source algorithm satisfies it
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 41, Lemma 28. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Learning
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_28 {X : Type*} {q : ℕ} (hq : 1 ≤ q) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : Learner X q) (hM : IsDP M ε δ) (μ : PMF (X × Bool)) :
    expectedPopulation μ M ≤ ENNReal.ofReal (Real.exp ε) * expectedSampleError μ M +
      ENNReal.ofReal δ := by sorry

end PrivPACLower.ICP
