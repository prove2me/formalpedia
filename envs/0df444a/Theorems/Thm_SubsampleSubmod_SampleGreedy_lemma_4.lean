-- Prove2me | Theorems.Thm_SubsampleSubmod_SampleGreedy_lemma_4
-- name    : SubsampleSubmod.SampleGreedy.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:56.464752+00:00
-- url     : https://prove2.me/theorems/8764cb13-e7ac-4b5e-81d8-269d31c03035
-- title:
--   Lemma 4, p. 10 — SampleGreedy and Algorithm 2 produce output sets with the same probability distribution
-- statement:
--   Let $\mathcal N$ be a finite ground set with a fixed linear order, $f$ any set function, $\mathcal I$ any family of sets, $T$ any set and $q$ a real number. Let $S^1$ be the output of SampleGreedy with sampling probability $q$ and $S^2$ the output of Algorithm 2 run from $O = T$, whose coins show $1$ independently with probability $q$. Then for every set $R \subseteq \mathcal N$,
--   $$\Pr[S^1 = R] \;=\; \Pr[S^2 = R],$$
--   that is,
--   $$\sum_{\mathcal N'} q^{|\mathcal N'|}(1-q)^{n-|\mathcal N'|}\,[\mathrm{SampleGreedy}(\mathcal N') = R] \;=\; \sum_{B} q^{|B|}(1-q)^{n-|B|}\,[S^2(B) = R].$$
--
--   This lemma transfers every guarantee proved for Algorithm 2 to SampleGreedy.
--
--   **Formalization Note** The identity is stated for every real $q$, every $T$ and every $\mathcal I$, which includes the paper's setting ($q \in [0,1]$, $T = \mathrm{OPT} \in \mathcal I$). Both algorithms break ties by the same fixed order of the ground set, as the paper assumes on p. 10.
-- source:
--   Harshaw et al., arXiv:2104.02772v1, p. 10, Lemma 4 (proof pp. 10–11)

import Mathlib
import Definitions.Def_SubsampleSubmod_SampleGreedy_Analysis

namespace SubsampleSubmod.SampleGreedy

/-- Lemma 4 (p. 10). The output `S¹` of SampleGreedy and the output `S²` of Algorithm 2 (run with any
comparison set `T`) have the same distribution: for every set `R`, `Pr[S¹ = R] = Pr[S² = R]`, both
computed with the independent sampling probability `q`. -/
theorem lemma_4 {α : Type} [Fintype α] [LinearOrder α] (f : Finset α → ℝ)
    (I : Finset α → Prop) (q : ℝ) (T R : Finset α) :
    ∑ N' : Finset α, sampleWeight q N' * (if sampleGreedy f I N' = R then (1 : ℝ) else 0) =
      ∑ B : Finset α, sampleWeight q B * (if (alg2 f I T B).S = R then (1 : ℝ) else 0) := by sorry

end SubsampleSubmod.SampleGreedy
