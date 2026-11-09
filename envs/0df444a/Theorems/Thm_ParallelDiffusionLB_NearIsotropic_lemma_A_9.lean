-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_9
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:14.132203+00:00
-- url     : https://prove2.me/theorems/f85d13d5-7699-42fa-bd9a-93221cc7500d
-- title:
--   Lemma A.9 — One new block per round
-- statement:
--   For every fixed $\gamma>0$ there exists $C(\gamma)>0$ such that, under the dimensions, prescribed valid codebook sizes and budgets of Lemma A.7, $H$ satisfying `LargeH`, and adjacent rate gaps exceeding $C(\gamma)(\sqrt{H/m}+H/m)$, the following holds for the independent codebook law. For every randomized measurable algorithm using $0\le R<B$ rounds and at most $P$ queries per round, couple the full interaction and the progressive interaction on the same codebooks and seed. Their transcripts and outputs satisfy
--   $$\Pr[T_R\ne\widetilde T_R]\le RPB\delta,\qquad\Pr[Y\ne\widetilde Y]\le RPB\delta.$$
--   The simulated transcript and output depend only on the independent seed and $S_1,\ldots,S_R$. Probabilities average over both sources of randomness. The simulation is the one defined by the truncations (37); no algorithm is restricted to interacting with it in the actual experiment.
--
--   Differences from the source:
--   - encoding: d coordinates in B consecutive blocks and d−Bm padding coordinates, m=⌊d/B⌋ → Layout with d=B*m+pad and an explicit hypothesis m=d/B when the source uses that convention; reason: this labels the same coordinates; padding may be zero and the empty product is one
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: at most P queries per round and an independent random seed → P query slots, measurable batch and output maps, and an arbitrary probability seed space; reason: unused slots can be filled with a fixed legal query and ignored; all finite-round measurable algorithms have this representation
--   - generalization: H given by (13) with a sufficiently large implicit constant → any H satisfying the four explicit LargeH inequalities from pp. 25–26; reason: the choice (13) satisfies these inequalities uniformly; the proofs use only these bounds
--   - encoding: there are coupled simulated variables → the explicitly computed progressive interaction on the same seed and codebooks; reason: this is the coupling in the proof on p. 27, with the same disagreement and prefix conclusions
--   - encoding: the interaction transcript of queries and answers → the table of answers, with all queries reconstructed from the fixed seed and earlier answers; reason: under the same seed, equality of answer tables is equivalent to equality of the full query-and-answer transcript
--   - generalization: prefix dependence for the nonempty codebooks in the instance law → pointwise prefix dependence for every tuple of finite codebooks, including empty codebooks outside the instance support; reason: the explicit truncation retains only prefix blocks even on these total-definition extensions; the probability bounds still use the prescribed nonempty codebooks
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.9, p. 24

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product
import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Simulation

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- The simulated variables are given explicitly by the progressive interaction of the paper's proof. -/
theorem lemma_A_9 (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Layout) (n : Fin L.B → ℕ) (P : ℕ)
      (ε ρ H : ℝ), L.m = L.d / L.B → 2 ≤ L.m → Real.sqrt 2 * γ ≤ L.m →
      L.sizesValid n → 1 ≤ P → 0 < ε → ε ≤ 1 → 0 < ρ → ρ ≤ 1/10 →
      LargeH L.d L.m L.B P γ ε ρ H → L.separated n H C →
      ∀ R : ℕ, ∀ hR : R < L.B,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
        (A : ParallelAlgorithm (Query L.d) (E L.d) (E L.d) Ω P R),
      let trunc := fun (r : Fin L.B) (S : L.Books) => L.truncated γ ε ρ S (r.val+1)
      let hRn : R ≤ L.B := Nat.le_of_lt hR
      ((L.instanceLaw n).prod ν).real {Sω |
        A.transcript (fun _ => L.oracle γ ε ρ Sω.1) Sω.2 ≠
          progressiveTranscript A hRn trunc Sω} ≤ R * P * L.B * hidingBudget L.d P ρ ∧
      ((L.instanceLaw n).prod ν).real {Sω |
        A.result (fun _ => L.oracle γ ε ρ Sω.1) Sω.2 ≠
          progressiveResult A hRn trunc Sω} ≤ R * P * L.B * hidingBudget L.d P ρ ∧
      DependsOnPrefix R (progressiveTranscript A hRn trunc) ∧
      DependsOnPrefix R (progressiveResult A hRn trunc) := by sorry

end ParallelDiffusionLB.NearIsotropic
