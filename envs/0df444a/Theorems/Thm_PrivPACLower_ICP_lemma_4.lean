-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_4
-- name    : PrivPACLower.ICP.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:52.281863+00:00
-- url     : https://prove2.me/theorems/eef8a5e1-1ed9-4368-9be3-f0668ad7c9f8
-- title:
--   Lemma 4 — adaptive parallel composition on arbitrary fixed blocks
-- statement:
--   Split a database into $k$ blocks at fixed positions, with arbitrary lengths $m_1,\ldots,m_k$. At stage $i$, a Markov kernel reads only block $i$ and the complete history of earlier outputs. Suppose every such stage is $(\varepsilon,\delta)$-DP as a function of its own block for each fixed history, where $\varepsilon>0$ and $0\le\delta<1$. Then the law obtained by composing these kernels with fresh randomness is a probability mechanism and
--
--   $$M(D)=(o_1,\ldots,o_k)\quad\text{is }(\varepsilon,\delta)\text{-DP}.$$
--
--   This permits adaptive dependence on earlier releases while charging privacy only to the one block containing the changed record. Empty blocks and an empty family are included.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: randomized adaptive maps and fresh independent randomness → measurable Markov kernels composed in chronological order; reason: kernels express the standard probability-law meaning of randomized maps; no independence between later outputs and earlier outputs is imposed
--   - encoding: a tuple of heterogeneous outputs and blocks at fixed positions → nested products for histories, with the dependent block index flattened by finSigmaFinEquiv; reason: each finite family of output types extends to a natural-number family; unused types do not affect the law
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 11, Lemma 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Reductions
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_4 {Z : Type*} {k : ℕ} (m : Fin k → ℕ)
    (O : ℕ → Type*) [∀ t, MeasurableSpace (O t)]
    (K : ∀ i : Fin k, (Fin (m i) → Z) → Kernel (History O i.val) (O i.val))
    [hK : ∀ i d, IsMarkovKernel (K i d)]
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 ≤ δ ∧ δ < 1)
    (hpriv : ∀ i (p : History O i.val),
      IsDP (fun d => (⟨K i d p, by infer_instance⟩ : ProbabilityMeasure (O i.val))) ε δ) :
    ∃ A : Mechanism Z (History O k) (∑ i, m i),
      (∀ d, (A d : Measure (History O k)) = adaptiveLaw m O K d k) ∧ IsDP A ε δ := by sorry

end PrivPACLower.ICP
