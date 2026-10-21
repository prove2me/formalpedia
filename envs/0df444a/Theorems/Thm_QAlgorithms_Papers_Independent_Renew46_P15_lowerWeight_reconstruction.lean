-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_lowerWeight_reconstruction
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.lowerWeight_reconstruction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:16:46.194954+00:00
-- url     : https://prove2.me/theorems/1775333d-c179-4c29-99a3-b92875de168f
-- title:
--   Full-rank lower-weight CG reconstruction
-- statement:
--   Fix an integer $N\ge2$ and two arbitrary finite-dimensional irreducible representations $S,S^\prime$ of $\mathrm{SU}(N)$, with normalized weakly decreasing integral top rows ending in zero. Use their orthonormal Gelfand–Tsetlin (GT) bases, without normalizing lower rows, and the real CG coefficients intertwining the common complexified Lie-algebra generators. These same coefficients apply to $\mathrm{SL}(N,\mathbb C)$.
--
--   Fix an output copy $(T,\alpha)$ and an occurring z-weight $W\ne W_z(H_T)$. Let $\mathcal M_T(W)$ be all GT-patterns in $T$ of weight $W$, and put $I_T(W)=|\mathcal M_T(W)|$. Assume that every parent expansion has already been computed correctly. Index rows by all triples $(M^{\prime\prime},k,l)$ for which $M^{\prime\prime}\in\mathcal M_T(W)$ and $P=M^{\prime\prime}+M^{k,l}$ is a valid parent; keep repeated occurrences of a parent. Form
--
--   $$
--    B_{(M^{\prime\prime},k,l),M^{\prime\prime\prime}}
--    =\langle M^{\prime\prime\prime}|J_{-,T}^{(l)}|P\rangle.
--   $$
--
--   Let $R$ contain the product-basis coefficients of applying the product lowering generator to each known parent expansion. Then
--
--   $$
--    \operatorname{rank}B=I_T(W),\qquad BX=R
--   $$
--
--   is consistent and has a unique solution $X$, namely the actual CG coefficient rows of all target patterns in $\mathcal M_T(W)$ for copy $\alpha$. The claim supplies exact reconstruction from known parents even though the list of equations can be redundant and rectangular.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 12, §XI, Eqs.(38)–(40), continuation p.13

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- XI, (38)-(40), PDF pp.12-13: correctly known parents give a consistent
full-column-rank system whose unique solution is the actual lower-weight CGCs.
No equality between number of listed equations and inner multiplicity is used. -/
theorem lowerWeight_reconstruction {n r : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t) (j : Fin r)
    (w : Fin (n + 1) → ℝ) (occurs : Nonempty (WeightPatterns (t j) w))
    (lower : w ≠ highestZ (t j))
    (parents : Matrix (ParentOccurrences (t j) w) (Pattern s × Pattern sPrime) ℝ)
    (parents_correct : ∀ p q, parents p q = c.coeff ⟨j, p.val.2.2.2⟩ q) :
    (reconstructionMatrix (t j) w).rank = Fintype.card (WeightPatterns (t j) w) ∧
    (reconstructionMatrix (t j) w) *
        (Matrix.of (fun (m : WeightPatterns (t j) w) (q : Pattern s × Pattern sPrime) =>
          c.coeff ⟨j, m.val⟩ q) :
          Matrix (WeightPatterns (t j) w) (Pattern s × Pattern sPrime) ℝ) =
        reconstructionRHS s sPrime (t j) w parents ∧
    ∀ x : Matrix (WeightPatterns (t j) w) (Pattern s × Pattern sPrime) ℝ,
      reconstructionMatrix (t j) w * x = reconstructionRHS s sPrime (t j) w parents →
        x = (fun (m : WeightPatterns (t j) w) (q : Pattern s × Pattern sPrime) =>
          c.coeff ⟨j, m.val⟩ q) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
