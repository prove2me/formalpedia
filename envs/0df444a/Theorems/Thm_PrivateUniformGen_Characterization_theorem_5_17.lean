-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_theorem_5_17
-- name    : PrivateUniformGen.Characterization.theorem_5_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:58.217821+00:00
-- url     : https://prove2.me/theorems/b23292fb-7340-4c6b-83ab-0630548df33f
-- title:
--   Theorem 5.17 — Excluding input examples by a second sampling stage
-- statement:
--   Let $X$ be countable and let $A$ be an $(\varepsilon,\delta)$-private mechanism on length-$n$ inputs, with infinite output almost surely on every input. For every $\eta>0$, there are a measurable second-stage family of probability laws $\kappa_S(K)$ and a mechanism $B$ whose law is obtained by first sampling $K\sim A(S)$ and then sampling from $\kappa_S(K)$. They satisfy
--
--   $$\Pr_{K\sim A(S),\ Z\sim\kappa_S(K)}[|Z|=\infty\ \text{and}\ Z\subseteq K\setminus\widehat S]=1,$$
--
--   on every input, and $B$ is $(\varepsilon,\delta+\eta)$-private. In particular its output is almost surely infinite on every input. The second stage may depend on the input, as does the source's exclusion operation.
--
--   Differences from the source:
--   - reading: measurable subsets of the output range → the product sigma-algebra on subsets of X; randomized algorithms are arbitrary maps to probability laws; reason: membership events generate this sigma-algebra; X is countable, all stated utility events are measurable, and the upper-bound laws have finite support; no computability requirement is imposed by the source
--   - encoding: randomized algorithms and probability-one guarantees → ProbabilityMeasure-valued maps and almost-everywhere predicates; reason: bundles probability one for every input and expresses the identical almost-sure events without allowing zero measures
--   - encoding: first samples K = A(S), then returns an infinite subset of K minus the input → a measurable ProbabilityMeasure-valued second stage with B(S) equal to its measure bind against A(S); reason: retains the two-stage law and its conditional almost-sure subset guarantee
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Theorem 5.17, p. 20. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Bounds

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem theorem_5_17 {X : Type} [Countable X] {n : ℕ}
    (A : Mechanism X (Set X) n) (ε δ : ℝ)
    (hDP : IsDP A ε δ) (hinf : InfiniteEveryInput A) (η : ℝ) (hη : 0 < η) :
  ∃ (B : Mechanism X (Set X) n)
    (κ : (Fin n → X) → Set X → ProbabilityMeasure (Set X)),
    (∀ S, Measurable (κ S)) ∧
    (∀ S, (B S : Measure (Set X)) =
      (A S : Measure (Set X)).bind (fun K => (κ S K : Measure (Set X)))) ∧
    (∀ S, ∀ᵐ K ∂(A S : Measure (Set X)),
      ∀ᵐ Z ∂(κ S K : Measure (Set X)), Z.Infinite ∧ Z ⊆ K \ Set.range S) ∧
    IsDP B ε (δ + η) ∧ InfiniteEveryInput B := by sorry

end PrivateUniformGen.Characterization
