-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_8
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:52.391205+00:00
-- url     : https://prove2.me/theorems/e230b25f-6a7b-4663-93ee-439434caeb3d
-- title:
--   Lemma A.8 — Fixed-instance local estimates
-- statement:
--   Fix the one-block parameters of Lemma A.7: $B\ge1$, $\gamma>0$, $m\ge\max\{2,\sqrt2\gamma\}$, $0<\varepsilon\le1$, $0<\rho\le1/10$, and budgets $\eta=\varepsilon/(8B)$ and $\zeta$ from (12). For every nonempty $S\subseteq V_m$ and $\tau\ge\gamma$,
--   $$p_\tau^S[a_\tau^S=1]\ge1-\zeta(\tau),\qquad E_{p_\tau^S}\|b_\tau^S-s_\tau^S\|^2\le\eta^2/(4\tau^2),\qquad \|b_\tau^S(x)-s_\tau^0(x)\|\le2\sqrt m/\tau^2\quad(\forall x).$$
--   These are fixed-instance statements; no random codebook assumption is imposed.
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: nonnegative expectations and KL divergence → nonnegative Lebesgue integrals and Mathlib KL divergence valued in [0,∞]; reason: all values for the stated Gaussian mixtures are finite and the inequalities are unchanged; a divergent error cannot default to zero
--   - encoding: a supremum over query points of a norm or probability → the corresponding bound at every query point; reason: these bounds are equivalent and avoid real supremum defaults on unbounded sets
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.8, p. 23

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_8 (m B : ℕ) (hB : 1 ≤ B) (γ ε ρ : ℝ)
    (hγ : 0 < γ) (hm : 2 ≤ m) (hmg : Real.sqrt 2 * γ ≤ m)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/10)
    (S : Finset (Cube m)) (hS : S.Nonempty) (τ : ℝ) (hτ : γ ≤ τ) :
    1 - gateBudget m B ε ρ τ ≤ (blockLaw S τ).real {x | gate B ε ρ S τ x = 1} ∧
    squaredError (blockLaw S τ) (localAnswer B ε S τ) (blockScore S τ) ≤
      ENNReal.ofReal (localBudget B ε ^ 2 / (4 * τ ^ 2)) ∧
    ∀ x, ‖localAnswer B ε S τ x - nullScore m τ x‖ ≤ 2 * Real.sqrt m / τ ^ 2 := by sorry

end ParallelDiffusionLB.NearIsotropic
