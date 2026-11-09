-- Prove2me | Theorems.Thm_PhyloCSP_theorem_3_2
-- name    : PhyloCSP.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:26:49.011821+00:00
-- url     : https://prove2.me/theorems/8d2dd0a4-fcd7-4a84-8671-9055903414a3
-- title:
--   Theorem 3.2 — reduction to consistent transformations and approximation by finite mixtures of basic transformations
-- statement:
--   Let $p(\Pi,F)$ be the guarantee of a tree transformation $F$ for a constraint language $\Pi$ (eq. (1)), and $d_{\mathrm{TV}}$ total variation distance.
--
--   1. For every tree transformation $F$ there is a consistent tree transformation $\hat F$ such that
--   $$
--   p(\Pi,\hat F)\ \ge\ p(\Pi,F)\qquad\text{for every constraint language }\Pi .
--   $$
--   2. For every consistent tree transformation $F$, every integer $k\ge 3$ and every $\delta>0$, there is a finite mixture $G$ of basic transformations such that
--   $$
--   d_{\mathrm{TV}}\bigl(F[P],G[P]\bigr)\le\delta\qquad\text{for every input pattern }P\text{ on at most }k\text{ leaves},
--   $$
--   and, in particular, $p(\Pi,G)\ge p(\Pi,F)-\delta$ for every constraint language $\Pi$ whose predicates have arity at most $k$.
--
--   Part 1 says that consistent transformations lose nothing in the framework; part 2 says that finite mixtures of basic transformations, whose output can be sampled in polynomial time, achieve the best guarantee of the framework up to any additive loss. In part 1 a single $\hat F$ works for all languages simultaneously. In part 2 the mixture $G$ is a tree transformation whose output law is exactly a finite mixture of basic transformations, with arbitrary templates and arbitrary centrally symmetric orientation laws.
--
--   **Formalization Note** Guarantees take values in $[0,\infty]$; the subtraction truncates at $0$.
--
--   Differences from the source:
--   - generalization: constraint languages without always-true or always-false predicates (Section 2 convention) → every finite nonempty family of predicates of any arities; reason: Definition 1.2 permits such predicates and Section 2 only assumes their absence without loss of generality; the statement for all languages specializes to the restricted ones
--   - encoding: finite rooted binary trees up to label-preserving isomorphism, arbitrary leaf labels → patterns as rooted-triplet relations satisfying the axioms of Section 7.1 on finite leaf sets S ⊆ ℕ (S = ∅ included, with its single pattern); reason: the paper's own characterization (pp.1, 18); relabeling equivariance makes labels in ℕ cover every tree; the empty leaf set adds no constraint
--   - encoding: predicates as Boolean formulas in triplet atoms → their satisfying sets Sat(φ) on the variables Fin k; reason: p.1: every predicate is determined by Sat(φ) and every set of patterns is a predicate
--   - encoding: probabilities and guarantees in [0,1], with p(Π,F) − δ a real number → values in ℝ≥0∞ with truncated subtraction and the empty infimum ⊤; reason: same values whenever the infimum is over a nonempty set; when p(Π,F) − δ < 0 both inequalities are trivially true
--   - encoding: a finite mixture of basic transformations (Definition 3.3, steps 1–4, arbitrary ±1 child labels) → a tree transformation whose output law equals Σᵢ λᵢ·(basic law) on every input, the basic law given by the triplet relation of the output for fixed random choices, with the child containing the least leaf labeled +1; reason: steps 2–4 determine the output's clusters; p.8: the law does not depend on the labeling since ν is centrally symmetric
--   - encoding: a constraint language (a finite nonempty set of predicates) → a finite nonempty indexed family (ConstraintLanguage) of predicates; reason: repetitions change no minimum over the language; every finite nonempty set is such a family
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 3.2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_PhyloCSP_Consistent
import Definitions.Def_PhyloCSP_pPred
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_PhyloCSP_IsMixtureOfBasic

set_option autoImplicit false

open scoped ENNReal

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Theorem 3.2, p.8 (PDF p.10): "(i) For every tree
transformation F, there exists a consistent transformation F̂ such that p(Π, F̂) ≥ p(Π, F) for every
constraint language Π. (ii) For every consistent F, k ≥ 3, and desired precision δ > 0, there
exists a finite mixture G of basic transformations such that dTV(F[P], G[P]) ≤ δ for every input
pattern P on at most k leaves. In particular, for every constraint language Π with predicates of
arity at most k, p(Π, G) ≥ p(Π, F) − δ."

**Formalization Note.** Both parts, as one conjunction. In (i) one `F̂` serves every constraint
language (∃ F̂ ∀ Π). In (ii) `G` is a tree transformation whose output law is *exactly* a finite
mixture of basic transformations (`IsMixtureOfBasic`), with arbitrary templates (unary or binary
internal nodes) and arbitrary centrally symmetric orientation laws; "on at most k leaves" covers
every leaf set of size `≤ k`. Guarantees are in `ℝ≥0∞`, where `−` truncates at `0` (both sides are
at most `1` unless an always-false predicate makes them `⊤`). `d_TV` is the published
`SamplingAC0.tvDist`, `½ Σ_ω |ρ(ω) − ρ′(ω)|` (the formula of Section 2, p.7). -/
theorem theorem_3_2 :
    (∀ F : TreeTransformation, ∃ Fh : TreeTransformation, Consistent Fh ∧
      ∀ L : ConstraintLanguage, pLang F L ≤ pLang Fh L) ∧
    (∀ F : TreeTransformation, Consistent F → ∀ k : ℕ, 3 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ G : TreeTransformation, (∃ m maxV : ℕ, IsMixtureOfBasic G m maxV) ∧
        (∀ (S : Finset ℕ), S.card ≤ k → ∀ P : Pattern ↥S,
          SamplingAC0.tvDist (F.law S P) (G.law S P) ≤ δ) ∧
        ∀ L : ConstraintLanguage, (∀ i, L.arity i ≤ k) →
          pLang F L - ENNReal.ofReal δ ≤ pLang G L) := by sorry

end PhyloCSP
