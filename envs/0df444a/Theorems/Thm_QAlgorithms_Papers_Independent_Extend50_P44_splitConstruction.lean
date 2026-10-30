-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P44_splitConstruction
-- name    : QAlgorithms.Papers.Independent.Extend50.P44.splitConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:11:06.422709+00:00
-- url     : https://prove2.me/theorems/493096d4-d59e-402e-9ab7-0103ea045984
-- title:
--   §2.2: split data-loading circuit before amplification (19)–(20)
-- statement:
--   Fix a compatible padded base scheme with supported sparsities $S_c,S_r$, and a real data table with positive maximum magnitude $M_a$. All active structural entries are nonzero; padding uses the stated zero-support convention. Let $0\le p\le1$. Replace the data rotation by two independent flagged rotations with selected amplitudes $\operatorname{sgn}(a_j)|a_j|^p/M_a^p$ and $|a_j|^{1-p}/M_a^{1-p}$.
--
--   The resulting unitary circuit (19) satisfies
--   $$ (\langle0|\otimes I)U_p(|0\rangle\otimes I)=\frac{A}{\sqrt{S_cS_r}M_a}, $$
--   the same selected block as circuit (16). It has two data-loading stages, hence $2D$ supplied-item loads. This is the exact split before any singular-value amplification.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, PDF p. 8, §2.2: split data-loading circuit before amplification (19)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

variable {n s d m : ℕ}

/-- PDF p.8, (19)-(20): splitting the rotation retains every selected entry
and the normalization; zero padding follows the explicit support convention. -/
theorem splitConstruction (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (active : Finset (Fin (2 ^ d))) (hactive : active.Nonempty)
    (hpadding : ∀ j, j ∉ active → a j = 0)
    (ha : 0 < tableMax a) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hnz : ∀ l, B.valid l = true → a l.1 ≠ 0) :
    QAlgorithms.IsBlockEncoding ((false, false, false), 0) (B.splitCircuit a p)
      (B.baseAlpha a) 0 (B.matrix a) ∧
    (∀ i j, B.splitCircuit a p (((false, false, false), 0), i)
      (((false, false, false), 0), j) =
      B.baseCircuit a false (((false, false), 0), i) (((false, false), 0), j)) ∧
    loadingCost (doubleLoadingSchedule active.card) = 2 * active.card := by sorry

end QAlgorithms.Papers.Independent.Extend50.P44

end
