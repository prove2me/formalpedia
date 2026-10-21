-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_complements
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_complements
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:57:12.320243+00:00
-- url     : https://prove2.me/theorems/e8877d3f-a516-4647-a84d-c00c4f993425
-- title:
--   §III (3.10)–(3.13): symplectic complements
-- statement:
--   Let $n\ge1$ and let $V$ be a real vector space of dimension $2n$, with a nondegenerate alternating bilinear form $B$. For a subspace $W$, put $k=\dim W$, let $r(W)$ be the rank of $B|_{W\times W}$, and put $W^\perp=\{x:B(w,x)=0\text{ for all }w\in W\}$.
--
--   $$
--   (W^\perp)^\perp=W,\quad\dim W^\perp=2n-k,\quad r(W^\perp)=2(n-k)+r(W).
--   $$
--
--   There also exists a subspace whose intersection with its complement is nonzero and whose sum with its complement is proper. This is an existential possibility, not a universal assertion about every W.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 9, §III (3.10)–(3.13): symplectic complements

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.9, (3.10)–(3.13): complement involution, dimension, integer
rank identity, and existence of non-direct complements. Alternation identifies
Mathlib's right orthogonal with the source's left orthogonal. -/
theorem symplectic_complements (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (W : Submodule ℝ V) :
    B.orthogonal (B.orthogonal W) = W ∧
    Module.finrank ℝ (B.orthogonal W) + Module.finrank ℝ W = 2 * n ∧
    (symplecticRank B (B.orthogonal W) : ℤ) =
      2 * ((n : ℤ) - (Module.finrank ℝ W : ℤ)) + (symplecticRank B W : ℤ) ∧
    (∃ L : Submodule ℝ V, L ⊓ B.orthogonal L ≠ ⊥ ∧ L ⊔ B.orthogonal L ≠ ⊤) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
