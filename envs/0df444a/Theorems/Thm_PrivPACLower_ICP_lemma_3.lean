-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_3
-- name    : PrivPACLower.ICP.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:58.431021+00:00
-- url     : https://prove2.me/theorems/6ca9c002-07e1-4301-b01f-45f6c0dff1a3
-- title:
--   Lemma 3 — group privacy with the exact additive term
-- statement:
--   Let $M$ be an $(\varepsilon,\delta)$-DP mechanism on $n$ records, with $\varepsilon>0$ and $0\le\delta<1$. If databases $S,S'$ differ in exactly $r$ records, every measurable output event $E$ satisfies
--
--   $$\Pr[M(S)\in E]\le e^{r\varepsilon}\Pr[M(S')\in E]+\delta\sum_{s=0}^{r-1}e^{s\varepsilon}.$$
--
--   For databases differing in at most $r$ records, the same comparison holds with additive term $r e^{(r-1)\varepsilon}\delta$. The case $r=0$ includes identical databases and an empty sum. These comparisons provide the privacy guarantee for repetition and the two-point learner lower bound.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 11, Lemma 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Reductions
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_3 {Z O : Type*} [MeasurableSpace O] {n : ℕ}
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : Mechanism Z O n) (hM : IsDP M ε δ) :
    (∀ (S S' : Fin n → Z) (r : ℕ), hamming S S' = r →
      ∀ E : Set O, MeasurableSet E →
        (M S : Measure O).real E ≤ Real.exp ((r : ℝ)*ε) * (M S' : Measure O).real E +
          δ * ∑ s ∈ Finset.range r, Real.exp ((s : ℝ)*ε)) ∧
    (∀ (r : ℕ) (S S' : Fin n → Z), hamming S S' ≤ r →
      ∀ E : Set O, MeasurableSet E →
        (M S : Measure O).real E ≤ Real.exp ((r : ℝ)*ε) * (M S' : Measure O).real E +
          (r : ℝ) * Real.exp (((r : ℝ)-1)*ε) * δ) := by sorry

end PrivPACLower.ICP
