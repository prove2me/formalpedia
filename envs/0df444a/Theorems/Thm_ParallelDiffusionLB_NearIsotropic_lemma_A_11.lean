-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_11
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:58.503176+00:00
-- url     : https://prove2.me/theorems/9c528495-4bb2-4fe2-b3c5-e5131321bde2
-- title:
--   Lemma A.11 — Uniform transition width
-- statement:
--   For every $\gamma>0$ there is a constant $C(\gamma)>0$, independent of all dimensions, budgets and $\tau$, such that under the public dimension and budget conditions and the four sufficient inequalities on $H$, for every $\tau\ge\gamma$,
--   $$\kappa^-(\tau)\le\alpha_\tau\le\kappa^+(\tau),\qquad \kappa^+(\tau)-\kappa^-(\tau)\le C(\gamma)(\sqrt{H/m}+H/m).$$
--   The constant is quantified before $d,m,B,P,\varepsilon,\rho,H$ and the noise level. This retains noise-uniform transition control and both threshold comparisons.
--
--   Differences from the source:
--   - generalization: H given by (13) with a sufficiently large implicit constant → any H satisfying the four explicit LargeH inequalities from pp. 25–26; reason: the choice (13) satisfies these inequalities uniformly; the proofs use only these bounds
--   - generalization: the shared product layout has m=floor(d/B) → independent integers B and m with 1≤B≤d and max{2,sqrt(2)*gamma}≤m≤d, without m=floor(d/B) or B*m≤d; reason: these one-block estimates use d and B only in the numerical budgets; the proofs on pp. 25–26 require no product layout, and every source layout satisfies these bounds
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.11, p. 26

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_11 (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d m B P : ℕ, 2 ≤ m → 1 ≤ B → 1 ≤ P →
    Real.sqrt 2 * γ ≤ m → m ≤ d → B ≤ d →
    ∀ ε ρ H : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ ≤ 1/10 →
    LargeH d m B P γ ε ρ H → ∀ τ : ℝ, γ ≤ τ →
      lowerRate d m B P ε ρ τ ≤ informationLevel m τ ∧
      informationLevel m τ ≤ upperRate m γ H τ ∧
      upperRate m γ H τ - lowerRate d m B P ε ρ τ ≤ C * transitionScale m H := by sorry

end ParallelDiffusionLB.NearIsotropic
