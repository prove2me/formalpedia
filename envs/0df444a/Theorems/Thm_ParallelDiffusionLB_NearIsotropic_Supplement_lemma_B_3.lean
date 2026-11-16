-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_Supplement_lemma_B_3
-- name    : ParallelDiffusionLB.NearIsotropic.Supplement.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:19.35617+00:00
-- url     : https://prove2.me/theorems/7ab85ecb-86f2-4556-817d-2f21ed57691f
-- title:
--   Lemma B.3 — One new coordinate per round
-- statement:
--   Let $a,b\in\mathbb N$. For all sufficiently large $d$, every query budget $1\le P\le d^a$ and every score accuracy $d^{-b}\le\varepsilon\le1$, consider the box family (53)–(54) with labels $\theta_1,\dots,\theta_d$ independent and uniform on $[M]$, its gated oracle $\hat s^\theta$ (57) and its truncations $\hat s^{\theta,[r]}$ (61).
--
--   Let $R<d$, let $\omega$ be a random seed with an arbitrary probability law $\nu$ on a measurable space $\Omega$, independent of $\theta$, and let $A$ be any $R$-round adaptive parallel algorithm that submits at most $P$ queries $(x,\sigma)\in\mathbb R^d\times(0,\infty)$ per round. Couple the actual interaction, in which every round is answered by $\hat s^\theta$, with the progressive interaction, in which round $r$ is answered by $\hat s^{\theta,[r]}$, on the same $\theta$ and $\omega$. Then:
--
--   1. the actual and progressive transcripts disagree with probability at most $RP/M$;
--   2. the actual output $Y$ and the progressive output $\tilde Y$ disagree with probability at most $RP/M$;
--   3. the progressive transcript and the progressive output depend only on $(\theta_1,\dots,\theta_R)$ and $\omega$.
--
--   The probabilities are over the independent labels and the seed. This is the step of Theorem 4.1 showing that each round exposes at most one new coordinate.
--
--   **Formalization Note** Lean rounds are 0-indexed: round `r : Fin R` is the paper's round $r+1$ and is answered by `truncOracle (r.val + 1) θ`. The dependence clause is the published `DependsOnPrefix R`, which holds for every seed and every label vector.
--
--   Differences from the source:
--   - encoding: for sufficiently large d, with a polynomial budget P = poly(d) and an inverse-polynomial accuracy ε_score = poly(d)^{-1} fixed beforehand → ∀ a b : ℕ, ∃ d₀, ∀ d ≥ d₀, ∀ P with 1 ≤ P ≤ d^a, ∀ ε > 0 with d^{-b} ≤ ε; reason: every polynomial budget is eventually at most d^a and every inverse polynomial eventually at least d^{-b}, for some a, b; this is the shape of the published theorem_3_1
--   - reading: ε_score = poly(d)^{-1} (inverse-polynomial accuracy) → ε ≤ 1; reason: an inverse polynomial accuracy is at most 1 for large d; it is the standing regime of B.1 in which the parameters are defined
--   - encoding: coordinates i ∈ [d] and labels k ∈ [M], 1-indexed → i : Fin d and k : Fin M, 0-indexed (paper i = i.val + 1, paper k = k.val + 1); reason: Lean convention; same objects
--   - encoding: a randomized algorithm making at most P queries per round for R rounds, with a random seed → any ParallelAlgorithm (Query d) (E d) (E d) Ω P R with exactly P slots per round and any probability law ν on an arbitrary measurable seed space Ω; reason: at most P queries are encoded by repeating queries in the P slots; the published model of §2.2
--   - encoding: the progressive interaction answers round r with ŝ^{θ,[r]} (r 1-indexed) → Lean round r : Fin R (0-indexed) is answered by truncOracle (r.val + 1) θ through the published progressiveTranscript / progressiveResult; reason: index shift; same rounds and same oracles
--   - encoding: the probability averages over the independent labels and seed → the real measure under (Measure.pi of the uniform law on Fin M).prod ν; reason: independent uniform labels are the product law
--   - encoding: the progressive transcript and output depend only on (θ_1, …, θ_R) and the seed → DependsOnPrefix R for the progressive transcript and for the progressive result (equal values for every seed and every two label vectors agreeing on the first R coordinates); reason: the published dependence predicate; it holds deterministically, not only almost surely
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma B.3, p. 32 (truncated oracle (61), p. 32; proof pp. 32–33)

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Supplement_Box
import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Simulation

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic.Supplement

/-- Lemma B.3 (Complete version of Lemma 4.3), p. 32, in the regime of B.1/(53).
Labels `θ_1, …, θ_d` are independent uniform on `[M]` (`Measure.pi` of the uniform law on
`Fin M`), the seed has an arbitrary probability law `ν`, and `A` is any `R`-round algorithm with
`P` query slots per round, `R < d`. Lean round `r : Fin R` (0-indexed) is the paper's round
`r + 1` and is answered by `ŝ^{θ,[r+1]}`. The actual and progressive transcripts, and outputs,
disagree with probability at most `R P / M`; both progressive maps depend only on the first `R`
labels and the seed (for every label vector and every seed). -/
theorem lemma_B_3 (a b : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ P : ℕ, 1 ≤ P → P ≤ d ^ a →
    ∀ ε : ℝ, 0 < ε → (d : ℝ) ^ (-(b : ℤ)) ≤ ε → ε ≤ 1 →
    ∀ (R : ℕ) (hR : R < d) (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω)
      [IsProbabilityMeasure ν] (A : ParallelAlgorithm (Query d) (E d) (E d) Ω P R),
      let μ : Fin d → Measure (Fin (numIntervals d P)) :=
        fun _ => uniformFinset (Finset.univ : Finset (Fin (numIntervals d P)))
      let trunc : Fin d → (Fin d → Fin (numIntervals d P)) → Query d → E d :=
        fun r θ => truncOracle d P ε (r.val + 1) θ
      ((Measure.pi μ).prod ν).real {θω |
          A.transcript (fun _ => gatedOracle d P ε θω.1) θω.2 ≠
            progressiveTranscript (Θ := fun _ => Fin (numIntervals d P)) A hR.le trunc θω} ≤
        (R * P : ℝ) / numIntervals d P ∧
      ((Measure.pi μ).prod ν).real {θω |
          A.result (fun _ => gatedOracle d P ε θω.1) θω.2 ≠
            progressiveResult (Θ := fun _ => Fin (numIntervals d P)) A hR.le trunc θω} ≤
        (R * P : ℝ) / numIntervals d P ∧
      DependsOnPrefix R (progressiveTranscript (Θ := fun _ => Fin (numIntervals d P)) A hR.le trunc) ∧
      DependsOnPrefix R (progressiveResult (Θ := fun _ => Fin (numIntervals d P)) A hR.le trunc) := by sorry

end ParallelDiffusionLB.NearIsotropic.Supplement
