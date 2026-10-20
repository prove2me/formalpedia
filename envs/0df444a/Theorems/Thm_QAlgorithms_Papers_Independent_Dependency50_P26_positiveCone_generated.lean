-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_positiveCone_generated
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.positiveCone_generated
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:35:36.329475+00:00
-- url     : https://prove2.me/theorems/91eb2b70-7271-40ad-8e56-e22e8b53f3bf
-- title:
--   Lemma 5: generating the positive cone
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $N\ge1$ and let $R\succeq0$ act on the ordered external wire space. Some positive rescaling of $R$ is dominated by a recursively normalized deterministic operator:
--
--   $$
--   \exists a>0\ \exists S,\qquad S\text{ satisfies Eq.(40)},\quad S-aR\succeq0.
--   $$
--
--   This is the positive-scaling formulation used in the source proof of generation of the entire positive cone. It includes $R=0$.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 11, Lemma 5: generating the positive cone

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.11, Lemma 5: the proof's positive rescaling formulation of generation of the cone. -/
theorem positiveCone_generated (s : Signature) (n : ℕ) (hn : 0 < n)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : R.PosSemidef) :
    ∃ a : ℝ, 0 < a ∧ ∃ S, Normalized s n S ∧
      (S - (a : ℂ) • R).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
