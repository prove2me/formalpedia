-- Prove2me | Theorems.Thm_RamseyDisambig_Spherical_Supplement_theorem_3
-- name    : RamseyDisambig.Spherical.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:26:09.49874+00:00
-- url     : https://prove2.me/theorems/f1deca5c-fbcc-4d9a-9799-bd62fdc020d0
-- title:
--   Theorem 3 — Constant pure 2×2 submatrices, yet every disambiguation has VC-dimension ≥ k
-- statement:
--   For every $k\in\mathbb N$ there is a finite partial matrix $M$, with entries in $\{0,1,\star\}$, such that
--
--   1. every pure $2\times2$ submatrix of $M$ (two distinct rows, two distinct columns, all four entries specified) is constant;
--   2. every disambiguation $c$ of $M$, obtained by replacing each $\star$ independently by $0$ or $1$ and not required to be symmetric, satisfies
--   $$\operatorname{VC}(c)\ge k;$$
--   3. in particular, $M$ itself has VC-dimension at most $1$, where only specified entries count toward shattering.
--
--   The theorem shows that the strongest local restriction on pure $2\times2$ patterns does not prevent every disambiguation from being complex; it strengthens the forbidden-pattern obstruction and yields Corollary 4 on Littlestone dimension 1.
--
--   **Formalization Note** $M$ has rows `Fin a` and columns `Fin b`. The VC-dimension of $c$ is the published row-first `vcDim`; that of $M$ is the partial-matrix VC-dimension of this supplement. All three conclusions are stated in one conjunction.
--
--   Differences from the source:
--   - generalization: k ∈ ℕ, read as a positive integer → every k : ℕ, including k = 0; reason: the case k = 0 is automatic since VC-dimension and induced containment of the 0-vertex graph are trivial; it specializes to the source's k ≥ 1
--   - encoding: a finite partial matrix → rows Fin a and columns Fin b for some a, b : ℕ; reason: every finite matrix is indexed this way up to relabelling, and all three properties are invariant under relabelling
--   - encoding: partial matrices with entries in {0,1,⋆} and VC-dimension of a binary matrix → PartialMatrix = Row → Col → Option Bool (none = ⋆), row-first ℕ∞ vcDim, casting via Option.getD; reason: same matrices and the same supremum; rows are concepts and columns are points, as on p. 8
--   - encoding: pure 2 × 2 submatrix is constant → for distinct rows r₁ ≠ r₂ and distinct columns c₁ ≠ c₂ with four specified entries, the four values agree; reason: the definition of p. 2, footnote 1, and p. 4
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Theorem 3, p. 4 (restated p. 17, proof pp. 17–18) (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialVC

set_option autoImplicit false

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- Theorem 3, p. 4 (restated p. 17, proof pp. 17–18): all three conclusions, the
"in particular" clause included. Disambiguations need not be symmetric; VC-dimension of a
total matrix is row-first `vcDim`, of the partial matrix `partialVCDim` (specified entries). -/
theorem theorem_3 (k : ℕ) :
    ∃ (a b : ℕ) (M : PartialMatrix (Fin a) (Fin b)),
      PureTwoByTwoConstant M ∧
      (∀ c : Fin a → Fin b → Bool, IsDisambiguation M c →
        (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c) ∧
      partialVCDim M ≤ 1 := by sorry

end RamseyDisambig.Spherical.Supplement
