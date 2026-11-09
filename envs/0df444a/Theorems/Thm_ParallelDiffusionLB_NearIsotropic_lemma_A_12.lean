-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_12
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:17.132461+00:00
-- url     : https://prove2.me/theorems/a14476e6-4f35-4810-9577-759f518d1278
-- title:
--   Lemma A.12 — One-batch indistinguishability
-- statement:
--   For every fixed $\gamma>0$ there is $C(\gamma)>0$ such that under the dimensions, valid prescribed codebook sizes and budgets of Lemma A.7, with $H$ satisfying `LargeH` and adjacent rates separated by more than $C(\gamma)(\sqrt{H/m}+H/m)$, the following holds. Fix a round $r\in[B]$, any exposed prefix in its support, and any fixed batch of $P$ legal queries, including arbitrary locations and noise levels. Then over the independent suffix codebooks,
--   $$\Pr[\exists\text{ query in the batch on which the full and }r\text{-truncated answers differ}]\le PB\delta.$$
--   Fixing the seed and prefix fixes any allowed batch selection map, so the statement covers every such map and at most $P$ queries. No common event over all noise levels is assumed.
--
--   Differences from the source:
--   - encoding: d coordinates in B consecutive blocks and d−Bm padding coordinates, m=⌊d/B⌋ → Layout with d=B*m+pad and an explicit hypothesis m=d/B when the source uses that convention; reason: this labels the same coordinates; padding may be zero and the empty product is one
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: at most P queries per round and an independent random seed → P query slots, measurable batch and output maps, and an arbitrary probability seed space; reason: unused slots can be filled with a fixed legal query and ignored; all finite-round measurable algorithms have this representation
--   - generalization: H given by (13) with a sufficiently large implicit constant → any H satisfying the four explicit LargeH inequalities from pp. 25–26; reason: the choice (13) satisfies these inequalities uniformly; the proofs use only these bounds
--   - encoding: a batch determined by a fixed prefix and seed → every fixed batch under the supported-prefix suffix law; reason: after fixing both, its selected batch is fixed; quantifying every batch covers every selection map
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.12, p. 26

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product
import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Simulation

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_12 (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Layout) (n : Fin L.B → ℕ) (P : ℕ)
      (ε ρ H : ℝ), L.m = L.d / L.B → 2 ≤ L.m → Real.sqrt 2 * γ ≤ L.m →
      L.sizesValid n → 1 ≤ P → 0 < ε → ε ≤ 1 → 0 < ρ → ρ ≤ 1/10 →
      LargeH L.d L.m L.B P γ ε ρ H → L.separated n H C →
      ∀ r : Fin L.B, ∀ S : L.Books,
        PrefixInSupport (fun j => codebookLaw L.m (n j)) S r.val →
        ∀ batch : Fin P → Query L.d,
          (suffixLaw (fun j => codebookLaw L.m (n j)) S r.val).real
            {S' | ∃ p, L.oracle γ ε ρ S' (batch p) ≠
              L.truncated γ ε ρ S' (r.val+1) (batch p)} ≤
            P * L.B * hidingBudget L.d P ρ := by sorry

end ParallelDiffusionLB.NearIsotropic
