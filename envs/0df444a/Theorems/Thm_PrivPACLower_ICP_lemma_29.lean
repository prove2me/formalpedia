-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_29
-- name    : PrivPACLower.ICP.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:54.544326+00:00
-- url     : https://prove2.me/theorems/87e89f13-fd5c-43c0-bfda-3d29119afcd3
-- title:
--   Lemma 29 — privacy amplification by resampling with replacement
-- statement:
--   Let $M$ be an $(\varepsilon,\delta)$-DP mechanism on $n\ge1$ records, with $0<\varepsilon\le1$ and $0\le\delta<1$. For $N\ge2n$, draw $n$ records independently and uniformly with replacement from an $N$-record input and run $M$. The explicitly averaged law is a probability mechanism satisfying
--
--   $$\varepsilon'=\frac{6\varepsilon n}{N},\qquad \delta'=e^{6\varepsilon n/N}\frac{4n\delta}{N}.$$
--
--   The result converts a private learner into a private mechanism whose empirical guarantee holds on each realizable database.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: databases of size n in the learner setting → n at least one; reason: makes the paper's implicit positive sample-size convention explicit and ensures the resampling distribution is defined
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 42, Lemma 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Reductions
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_29 {Z O : Type*} [MeasurableSpace O] {n N : ℕ}
    (hn : 1 ≤ n) (hN : 2*n ≤ N) (ε δ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1) (hδ : 0 ≤ δ ∧ δ < 1)
    (M : Mechanism Z O n) (hM : IsDP M ε δ) :
    ∃ A : Mechanism Z O N, (∀ S, (A S : Measure O) = resampleLaw M S) ∧
      IsDP A (6*ε*(n : ℝ)/(N : ℝ))
        (Real.exp (6*ε*(n : ℝ)/(N : ℝ)) * 4*(n : ℝ)*δ/(N : ℝ)) := by sorry

end PrivPACLower.ICP
