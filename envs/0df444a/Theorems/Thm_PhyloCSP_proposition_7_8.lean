-- Prove2me | Theorems.Thm_PhyloCSP_proposition_7_8
-- name    : PhyloCSP.proposition_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:28:03.481082+00:00
-- url     : https://prove2.me/theorems/b24cfe6c-1e4c-4228-a9a3-38aa43376ea4
-- title:
--   Proposition 7.8 — every tree transformation yields a transformation of $\mathcal F$ at least as good
-- statement:
--   For every tree transformation $F$ there is a transformation $D$ of the Fraïssé limit $\mathcal F$ (a random binary tree structure on $Z$) such that
--   $$
--   p(\Pi,D)\ \ge\ p(\Pi,F)\qquad\text{for every constraint language }\Pi .
--   $$
--
--   This is the first step of the proof of Theorem 3.2(i): the guarantees of $F$ are transferred to a random relation on the universal structure, which is then symmetrized.
--
--   Differences from the source:
--   - generalization: constraint languages without always-true or always-false predicates (Section 2 convention) → every finite nonempty family of predicates of any arities; reason: Definition 1.2 permits such predicates and Section 2 only assumes their absence without loss of generality; the statement for all languages specializes to the restricted ones
--   - encoding: predicates as Boolean formulas in triplet atoms → their satisfying sets Sat(φ) on the variables Fin k; reason: p.1: every predicate is determined by Sat(φ) and every set of patterns is a predicate
--   - encoding: probabilities and guarantees in [0,1], with p(Π,F) − δ a real number → values in ℝ≥0∞ with truncated subtraction and the empty infimum ⊤; reason: same values whenever the infimum is over a nonempty set; when p(Π,F) − δ < 0 both inequalities are trivially true
--   - encoding: a probability distribution on ternary relations D on Z with every realization a binary tree structure → a probability measure on Z → Z → Z → Bool (product σ-algebra) giving full measure to tree relations; reason: a law on the closed set H of tree relations is the same as a law on all relations concentrated on H
--   - encoding: finite rooted binary trees up to label-preserving isomorphism, arbitrary leaf labels → patterns as rooted-triplet relations satisfying the axioms of Section 7.1 on finite leaf sets S ⊆ ℕ (S = ∅ included, with its single pattern); reason: the paper's own characterization (pp.1, 18); relabeling equivariance makes labels in ℕ cover every tree; the empty leaf set adds no constraint
--   - encoding: a constraint language (a finite nonempty set of predicates) → a finite nonempty indexed family (ConstraintLanguage) of predicates; reason: repetitions change no minimum over the language; every finite nonempty set is such a family
--   - encoding: the Fraïssé limit F = (Z, C) and its automorphism group Aut(F) → the concrete structure (Z, fraisseRel) of Definition 7.5, Z = Finset ℚ, and AutF its automorphism group; reason: Theorem 7.4 and Appendix B.1 identify the concrete structure with F, which is unique up to isomorphism; the statement is invariant under isomorphism
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Proposition 7.8, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_PhyloCSP_pPred
import Definitions.Def_PhyloCSP_TransformationOfF

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Proposition 7.8, p.21 (PDF p.23): "For every tree
transformation F, there exists a transformation D of F such that p(Π, D) ≥ p(Π, F) for every
constraint language Π."

**Formalization Note.** A transformation of `F` is a probability law `μ` on relations on `Z`
concentrated on tree relations (`IsTransformationOfF`); one `μ` serves every constraint
language. -/
theorem proposition_7_8 (F : TreeTransformation) :
    ∃ μ : Measure (Z → Z → Z → Bool), IsTransformationOfF μ ∧
      ∀ L : ConstraintLanguage, pLang F L ≤ pLangF μ L := by sorry

end PhyloCSP
