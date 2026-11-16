-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_lemma_18
-- name    : RamseyDisambig.Spherical.Supplement.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:25:40.559364+00:00
-- url     : https://prove2.me/theorems/5dde545d-669a-4c3b-acf7-5545c4f9f83e
-- title:
--   Lemma 18 — A tame partial matrix with two rich uniform fillings
-- statement:
--   For every $k\in\mathbb N$ there are finite index sets and a partial matrix $U$ over them such that
--
--   1. no row and no column of $U$ contains both a $0$ entry and a $1$ entry;
--   2. the matrices $U^{(0)}$ and $U^{(1)}$, obtained by casting every $\star$ of $U$ into $0$, respectively into $1$, both satisfy
--   $$\operatorname{VC}(U^{(0)})\ge k\qquad\text{and}\qquad \operatorname{VC}(U^{(1)})\ge k.$$
--
--   This tame matrix is the building block that Theorem 3 amplifies with the girth Ramsey theorem.
--
--   **Formalization Note** $U$ has rows `Fin a` and columns `Fin b`; the VC-dimension of a total matrix is the published row-first `vcDim` in `ℕ∞`.
--
--   Differences from the source:
--   - reading: there exists a partial matrix U (finiteness not stated) → a finite U with rows Fin a and columns Fin b; reason: the stronger reading: the proof's U is a 2^(k+1) × 2k matrix and Theorem 3 applies the girth Ramsey theorem to a finite graph built from it
--   - generalization: k ∈ ℕ, read as a positive integer → every k : ℕ, including k = 0; reason: the case k = 0 is automatic since VC-dimension and induced containment of the 0-vertex graph are trivial; it specializes to the source's k ≥ 1
--   - encoding: partial matrices with entries in {0,1,⋆} and VC-dimension of a binary matrix → PartialMatrix = Row → Col → Option Bool (none = ⋆), row-first ℕ∞ vcDim, casting via Option.getD; reason: same matrices and the same supremum; rows are concepts and columns are points, as on p. 8
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Lemma 18, p. 17 (proof p. 17) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialVC

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Lemma 18, p. 17. The witness is finite (the proof's `U` is `2^(k+1) × 2k`). -/
theorem lemma_18 (k : ℕ) :
    ∃ (a b : ℕ) (U : PartialMatrix (Fin a) (Fin b)),
      NoRowOrColumnMixed U ∧
      (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim (castStars U false) ∧
      (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim (castStars U true) := by sorry

end RamseyDisambig.Spherical.Supplement
