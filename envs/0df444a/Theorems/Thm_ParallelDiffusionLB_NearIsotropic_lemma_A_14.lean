-- Prove2me | Theorems.Thm_ParallelDiffusionLB_NearIsotropic_lemma_A_14
-- name    : ParallelDiffusionLB.NearIsotropic.lemma_A_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:53.166897+00:00
-- url     : https://prove2.me/theorems/5187c123-c39b-4afc-9815-02d4fee9404e
-- title:
--   Lemma A.14 — Recognizing samples from a hidden block
-- statement:
--   Use the one-block dimensions and budgets of Lemma A.7, fix $0<\kappa_{min}<\kappa_{max}<\alpha_\gamma$, and set $c_0=(\alpha_\gamma-\kappa_{max})/2$. Suppose $\gamma^{-1}\sqrt{8\log(1/\zeta(\gamma))/m}\le c_0$. For $1\le n\le2^m$ with $\log n/m\le\kappa_{max}$, each size-$n$ codebook satisfies
--   $$E(S)=\{x:a_\gamma^S(x)=1\}=\{x:\max_{y\in S}\ell_\gamma(y,x)\ge t_\gamma\},\qquad p_\gamma^S(E(S))\ge1-\zeta(\gamma).$$
--   For a uniformly random size-$n$ codebook, every fixed $x$ satisfies
--   $$\Pr_S[x\in E(S)]\le ne^{-t_\gamma}\le e^{-c_0m}.$$
--   For every independent random vector $V$ with any probability law, $\Pr[V\in E(S)]\le e^{-c_0m}$ as well. Both deterministic acceptance and randomized blindness, including the independent-vector consequence, are retained.
--
--   Differences from the source:
--   - encoding: nonempty subsets of {−1,+1}^m → finite sets of Boolean-labelled cube vertices with nonemptiness or positive prescribed cardinality; reason: the vertex map is a bijection and the uniform subset law samples without replacement
--   - encoding: a supremum over query points of a norm or probability → the corresponding bound at every query point; reason: these bounds are equivalent and avoid real supremum defaults on unbounded sets
--   - encoding: any random vector independent of S → every probability law for V, jointly distributed with S by the product law; reason: this is exactly independence and includes every possible marginal law
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, Lemma A.14, p. 27

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Product

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

theorem lemma_A_14 (m B n : ℕ) (hm : 2 ≤ m) (hB : 1 ≤ B)
    (γ ε ρ κmin κmax : ℝ) (hγ : 0 < γ) (hmg : Real.sqrt 2 * γ ≤ m)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/10)
    (hkmin : 0 < κmin) (hkk : κmin < κmax) (hkmax : κmax < informationLevel m γ)
    (hmargin : Real.sqrt (8 * Real.log (1 / gateBudget m B ε ρ γ) / m) / γ ≤
      (informationLevel m γ - κmax) / 2)
    (hn : 1 ≤ n) (hnm : n ≤ 2 ^ m) (hκ : rate m n ≤ κmax) :
    (∀ S : Finset (Cube m), S.card = n →
      recognizingEvent B ε ρ γ S = {x | cutoff m B ε ρ γ ≤ evidence S γ x} ∧
      1 - gateBudget m B ε ρ γ ≤ (blockLaw S γ).real (recognizingEvent B ε ρ γ S)) ∧
    (∀ x, (codebookLaw m n).real {S | x ∈ recognizingEvent B ε ρ γ S} ≤
      n * Real.exp (-cutoff m B ε ρ γ)) ∧
    (n : ℝ) * Real.exp (-cutoff m B ε ρ γ) ≤
      Real.exp (-((informationLevel m γ - κmax) / 2) * m) ∧
    (∀ νV : Measure (E m), IsProbabilityMeasure νV →
      (νV.prod (codebookLaw m n)).real {vS | vS.1 ∈ recognizingEvent B ε ρ γ vS.2} ≤
        Real.exp (-((informationLevel m γ - κmax) / 2) * m)) := by sorry

end ParallelDiffusionLB.NearIsotropic
