-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_canonical_basis
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.canonical_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:49:04.837292+00:00
-- url     : https://prove2.me/theorems/812e86c5-67b7-4b9c-aab4-fc728b32f1f7
-- title:
--   §1: canonical basis computation and equality test
-- statement:
--   Let $B$ be a full-rank integer $k\times k$ column basis. There is a unique matrix $C$ generating the same subgroup and satisfying
--
--   $$
--   c_{ij}=0\ (i>j),\qquad c_{ii}>0,\qquad 0\le c_{ij}<c_{ii}\ (i<j).
--   $$
--
--   A single classical polynomial-time procedure maps the signed binary encoding of $B$ to that of $C$, with output length polynomial in the actual input length. Another single polynomial-time procedure decides whether two such bases generate the same subgroup. Both procedures work for all dimensions.
--
--   Consequently, arbitrary-basis output and canonical-basis output are polynomially equivalent: normalize in one direction and retain the canonical basis in the other.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 4, §1: canonical basis computation and equality test

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.4: canonicalization, efficient equality testing, and the polynomial equivalence
of arbitrary-basis and canonical-basis output. Runtime is measured in the input's actual bit
length. Polynomial-time computability refers to a halting multi-stack Turing machine. -/
theorem canonical_basis :
    ∃ (normalize equal : List Bool → List Bool) (p : Polynomial ℕ),
      QAlgorithms.Complexity.PolyTimeComputable normalize ∧
      QAlgorithms.Complexity.PolyTimeComputable equal ∧
      ∀ (k : ℕ) (B : Matrix (Fin k) (Fin k) ℤ), IsLatticeBasis B →
        IsCanonicalBasis B (canonicalBasis B) ∧
        (∀ C, IsCanonicalBasis B C → C = canonicalBasis B) ∧
        normalize (encodeBasis B) = encodeBasis (canonicalBasis B) ∧
        (encodeBasis (canonicalBasis B)).length ≤ p.eval (encodeBasis B).length ∧
        ∀ C : Matrix (Fin k) (Fin k) ℤ, IsLatticeBasis C →
          equal (encodeBasis B ++ encodeBasis C) =
            [decide (columnLattice B = columnLattice C)] := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
