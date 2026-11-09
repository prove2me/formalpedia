-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_13
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:47.030114+00:00
-- url     : https://prove2.me/theorems/5cfdb681-e664-4eeb-a869-ee92c1bf29d2
-- title:
--   Lemma A.13 — Progressive simulation
-- statement:
--   Let $n,P\ge1$ and let $\Theta=(\Theta_1,\ldots,\Theta_n)$ have independent finite-valued coordinates with probability laws $\mu_j$. Let an arbitrary independent probability seed contain all algorithmic and output randomness. Fix measurable full and truncated oracles on their possible configurations, and $\delta_{batch}\ge0$. Assume each $r$-truncation depends only on the first $r$ coordinates on the support. Assume that for each fixed supported prefix of length $r-1$ and each fixed batch of at most $P$ queries, the independent suffix law gives full-versus-truncated disagreement probability at most $\delta_{batch}$.
--
--   For every $0\le R\le n$ and every measurable adaptive algorithm with $R$ rounds and $P$ slots per round, run the actual and progressive interactions with the same seed and configuration. Then
--   $$\Pr[T_R\ne\widetilde T_R]\le R\delta_{batch},\qquad \Pr[Y\ne\widetilde Y]\le R\delta_{batch}.$$
--   The progressive transcript and output depend only on the seed and first $R$ coordinates on the support. Query, answer and output spaces are arbitrary measurable spaces, with measurable equality on answers and outputs so these disagreement events are measurable. The case $R=0$ is included.
--
--   Differences from the source:
--   - encoding: at most P queries per round and an independent random seed → P query slots, measurable batch and output maps, and an arbitrary probability seed space; reason: unused slots can be filled with a fixed legal query and ignored; all finite-round measurable algorithms have this representation
--   - encoding: finite-valued independent random coordinates and probabilities of transcript or output inequality → finite discrete coordinate probability laws and measurable equality on answer and output spaces; dependence only on supported configurations; reason: product laws represent independence, and the source probabilities are ordinary measurable-event probabilities; all real query and output applications satisfy these conventions
--   - encoding: there is a coupling to the progressive interaction → the explicit same-seed same-configuration coupling in the proof; reason: the page constructs precisely these simulated variables
--   - encoding: the interaction transcript of queries and answers → the table of answers, with all queries reconstructed from the fixed seed and earlier answers; reason: under the same seed, equality of answer tables is equivalent to equality of the full query-and-answer transcript
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.13, p. 27

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Simulation

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Generic progressive simulation, with independent finite-valued coordinates and an arbitrary seed law.
The pointwise batch condition is exactly the condition obtained after fixing a prefix and seed. -/
theorem lemma_A_13 (n P : ℕ) (hn : 1 ≤ n) (hP : 1 ≤ P)
    (Θ : Fin n → Type*) [∀ j, Fintype (Θ j)] [∀ j, MeasurableSpace (Θ j)]
    [∀ j, MeasurableSingletonClass (Θ j)]
    (μ : (j : Fin n) → Measure (Θ j)) [∀ j, IsProbabilityMeasure (μ j)]
    (Q Ans Out : Type*) [MeasurableSpace Q] [MeasurableSpace Ans] [MeasurableSpace Out] [MeasurableEq Ans] [MeasurableEq Out]
    (O : ((j : Fin n) → Θ j) → Q → Ans)
    (trunc : Fin n → ((j : Fin n) → Θ j) → Q → Ans)
    (hO : ∀ θ, PrefixInSupport μ θ n → Measurable (O θ))
    (ht : ∀ r θ, PrefixInSupport μ θ n → Measurable (trunc r θ))
    (δbatch : ℝ) (hδ : 0 ≤ δbatch)
    (hprefix : ∀ r : Fin n, ∀ θ θ', PrefixInSupport μ θ n →
      PrefixInSupport μ θ' n → PrefixEq (r.val+1) θ θ' → trunc r θ = trunc r θ')
    (hbatch : ∀ r : Fin n, ∀ θ : (j : Fin n) → Θ j,
      PrefixInSupport μ θ r.val → ∀ batch : Fin P → Q,
        (suffixLaw μ θ r.val).real {θ' | ∃ p, O θ' (batch p) ≠ trunc r θ' (batch p)} ≤ δbatch)
    (R : ℕ) (hR : R ≤ n) (Ω : Type*) [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : ParallelAlgorithm Q Ans Out Ω P R) :
    ((Measure.pi μ).prod ν).real {θω |
      A.transcript (fun _ => O θω.1) θω.2 ≠ progressiveTranscript A hR trunc θω} ≤ R * δbatch ∧
    ((Measure.pi μ).prod ν).real {θω |
      A.result (fun _ => O θω.1) θω.2 ≠ progressiveResult A hR trunc θω} ≤ R * δbatch ∧
    SupportedDependsOnPrefix μ R (progressiveTranscript A hR trunc) ∧
    SupportedDependsOnPrefix μ R (progressiveResult A hR trunc) := by sorry

end ParallelDiffusionLB.NearIsotropic
