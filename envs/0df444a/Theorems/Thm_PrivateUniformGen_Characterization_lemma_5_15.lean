-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_lemma_5_15
-- name    : PrivateUniformGen.Characterization.lemma_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:43.559389+00:00
-- url     : https://prove2.me/theorems/8a433331-228f-44d3-9516-119d644e2551
-- title:
--   Lemma 5.15 — Block sensitivity and output stability
-- statement:
--   Let $X$ be countable and $C$ a nonempty, possibly uncountable family of infinite subsets of $X$.
--
--   Under the standing assumptions of Section 5, fix a public $m>\operatorname{CDim}(C)$. For neighboring length-$n$ datasets $S,S'$ and every augmented profile $\sigma\in\Xi$,
--
--   $$|\lambda_S(\sigma)-\lambda_{S'}(\sigma)|\le2.$$
--
--   Moreover, $\lambda_S(\sigma)>2$ implies $\lambda_{S'}(\sigma)>0$ and $\gamma_S(\sigma)=\gamma_{S'}(\sigma)$. The subtraction is signed. Thus every sufficiently long block has a stable associated set on a neighboring dataset.
--
--   Differences from the source:
--   - encoding: standing assumptions at the beginning of Section 5 → explicit nonnegative finite closure dimension and finite nested branching dimension; reason: these assumptions apply throughout the source section and are made visible in the theorem binders
--   - encoding: integer t in the public range and cardinality differences → natural t and m with t < N(C,m), with cardinality subtraction in the integers; reason: nonnegative source indices and positive public thresholds are unchanged; repetitions affect distinct support rather than input length
--   - encoding: recursive profiles and iterated cores → lists and recursion with initial fuel equal to the finite rank; reason: every nonterminal step strictly reduces positive rank, so fuel does not truncate any source profile; the terminal output is the core
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Lemma 5.15, p. 16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Robust

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem lemma_5_15 {X : Type} [Countable X] (C : LanguageClass X)
    (hc0 : 0 ≤ closureDim C) (hcf : closureDim C < ⊤) (hdf : nbDim C ⊤ < ⊤)
    (m : ℕ) (hm : (m : WithTop ℤ) > closureDim C)
    {n : ℕ} (S S' : Fin n → X) (hne : Neighbors S S')
    (σ : List ℕ) (hσ : σ ∈ augmentedXi C) :
  |(blockLength C m S σ : ℤ) - (blockLength C m S' σ : ℤ)| ≤ 2 ∧
  (2 < blockLength C m S σ →
    0 < blockLength C m S' σ ∧ blockOutput C m S σ = blockOutput C m S' σ) := by sorry

end PrivateUniformGen.Characterization
