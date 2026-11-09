-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_2
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:50.094986+00:00
-- url     : https://prove2.me/theorems/2c01e6f8-8742-4a86-8607-c498fd0c94d1
-- title:
--   Lemma A.2 — Near-isotropy
-- statement:
--   Fix $\kappa_{min},K>0$. There exist $c>0$ and $d_0\ge2$ such that for every layout with $d\ge d_0$, $m\ge d^{2/3}(\log d)^{1/3}/K$, valid prescribed sizes satisfying $\log n_j/m\ge\kappa_{min}$, and any $\gamma>0$, the independent uniform-codebook law obeys
--   $$\Pr_S[\|E_{\pi^S}X\|>d^{-10}\ \text{or}\ \|\operatorname{Cov}(\pi^S)-(1+\gamma^2)I_d\|_{op}>d^{-10}]\le e^{-cm}.$$
--   For arbitrary valid prescribed sizes and every $t\in(0,1]$, without the scale or rate bounds, the same probability with tolerance $t$ is at most
--   $$4m^2t^{-2}\sum_jn_j^{-1}.$$
--   The public choices of Lemma A.1 satisfy the scale and rate conditions for a fixed $K$. Both the exponential conclusion and the general explicit estimate are retained.
--
--   Differences from the source:
--   - encoding: d coordinates in B consecutive blocks and d−Bm padding coordinates, m=⌊d/B⌋ → Layout with d=B*m+pad and an explicit hypothesis m=d/B when the source uses that convention; reason: this labels the same coordinates; padding may be zero and the empty product is one
--   - generalization: exponential bound for the public parameters above → all positive block layouts with arbitrary nonnegative padding in the explicit estimate; the exponential clause uses only a public lower block-scale bound and valid sizes with rates at least kappa_min; reason: the proof uses only the independent block moments and, in the exponential clause, these scale and rate bounds; every A.1 choice with m=floor(d/B) is included
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.2, p. 19

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- The exponential clause applies to any public-scale blocks with rates bounded below;
the explicit clause retains arbitrary prescribed codebook sizes. -/
theorem lemma_A_2 (κmin K : ℝ) (hκ : 0 < κmin) (hK : 0 < K) :
    (∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, 2 ≤ d₀ ∧
      ∀ (L : Layout) (n : Fin L.B → ℕ) (γ : ℝ), d₀ ≤ L.d → 0 < γ →
      L.sizesValid n →
      ((L.d : ℝ) ^ (2/3 : ℝ) * Real.log L.d ^ (1/3 : ℝ)) / K ≤ L.m →
      (∀ j, κmin ≤ rate L.m (n j)) →
      (L.instanceLaw n).real {S | ¬ IsNearIsotropic (L.targetLaw S γ) γ ((L.d : ℝ) ^ (-10 : ℤ))} ≤
        Real.exp (-c * L.m)) ∧
    (∀ (L : Layout) (n : Fin L.B → ℕ) (γ t : ℝ), L.sizesValid n → 0 < γ →
      0 < t → t ≤ 1 →
      (L.instanceLaw n).real {S | ¬ IsNearIsotropic (L.targetLaw S γ) γ t} ≤
        4 * (L.m : ℝ) ^ 2 / t ^ 2 * ∑ j, (n j : ℝ)⁻¹) := by sorry

end ParallelDiffusionLB.NearIsotropic
