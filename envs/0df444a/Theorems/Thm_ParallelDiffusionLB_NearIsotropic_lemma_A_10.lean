-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_10
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:00.391259+00:00
-- url     : https://prove2.me/theorems/eaf9127b-260c-4451-ab7c-9c11700957e1
-- title:
--   Lemma A.10 — One-block hiding estimates
-- statement:
--   Use positive $\gamma$, integer dimensions $m\ge\max\{2,\sqrt2\gamma\}$ and $B,m\le d$, query budget $P\ge1$, $0<\varepsilon\le1$, $0<\rho\le1/10$, and $H$ satisfying the four sufficient inequalities in `LargeH`. Let $S$ be a uniform $n$-element subset of $V_m$, $1\le n\le2^m$, and $\kappa=\log n/m$. For every fixed $\tau\ge\gamma$,
--   $$\kappa\le\kappa^-(\tau)\ \Longrightarrow\ \Pr_S[a_\tau^S(x)>0]\le\delta\quad(\forall x),$$
--   $$\kappa\ge\kappa^+(\tau)\ \Longrightarrow\ \Pr_S[b_\tau^S\equiv s_\tau^0]\ge1-\delta.$$
--   The second event is equality of functions on all of $\mathbb R^m$. Both sparse and dense conclusions use the thresholds constructed in (38)–(39).
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: a supremum over query points of a norm or probability → the corresponding bound at every query point; reason: these bounds are equivalent and avoid real supremum defaults on unbounded sets
--   - generalization: H given by (13) with a sufficiently large implicit constant → any H satisfying the four explicit LargeH inequalities from pp. 25–26; reason: the choice (13) satisfies these inequalities uniformly; the proofs use only these bounds
--   - generalization: the shared product layout has m=floor(d/B) → independent integers B and m with 1≤B≤d and max{2,sqrt(2)*gamma}≤m≤d, without m=floor(d/B) or B*m≤d; reason: these one-block estimates use d and B only in the numerical budgets; the proofs on pp. 25–26 require no product layout, and every source layout satisfies these bounds
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.10, p. 25

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_10 (d m B P n : ℕ) (hm : 2 ≤ m) (hB : 1 ≤ B) (hP : 1 ≤ P)
    (hn : 1 ≤ n) (hnm : n ≤ 2 ^ m) (γ ε ρ H τ : ℝ)
    (hγ : 0 < γ) (hmg : Real.sqrt 2 * γ ≤ m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/10) (hd : m ≤ d) (hBd : B ≤ d)
    (hH : LargeH d m B P γ ε ρ H) (hτ : γ ≤ τ) :
    (rate m n ≤ lowerRate d m B P ε ρ τ → ∀ x,
      (codebookLaw m n).real {S | 0 < gate B ε ρ S τ x} ≤ hidingBudget d P ρ) ∧
    (upperRate m γ H τ ≤ rate m n →
      1 - hidingBudget d P ρ ≤
        (codebookLaw m n).real {S | localAnswer B ε S τ = nullScore m τ}) := by sorry

end ParallelDiffusionLB.NearIsotropic
