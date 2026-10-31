-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_nppt_exponential_separation
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.nppt_exponential_separation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:26:05.747626+00:00
-- url     : https://prove2.me/theorems/f2015118-6630-4d7d-864e-e902adf636ff
-- title:
--   §IV, unnumbered: exponential separation of NPPT from PPT alternatives
-- statement:
--   Let $\rho$ be a normalized state on nonzero finite-dimensional spaces $H_A\otimes H_B$, and assume its partial transpose on B is not positive semidefinite. Let $P_n$ be all normalized PPT states on the grouped blocks $H_A^{\otimes n}:H_B^{\otimes n}$. There exist a constant $c>0$, one sequence of effects $0\le A_n\le I$, and an integer $N$ such that
--   $$
--   \operatorname{Tr}[(I-A_n)\rho^{\otimes n}]\longrightarrow0,\qquad
--   \operatorname{Tr}(A_n\omega_n)\le2^{-cn}\quad(\forall n\ge\max\{N,1\},\ \forall\omega_n\in P_n).
--   $$
--
--   This states uniform eventual exponential separation; it does not specify an optimal exponent or replace PPT by separable alternatives.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 28, §IV, unnumbered: exponential separation of NPPT from PPT alternatives

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.28, unnumbered PPT consequence: vanishing rejection and a uniform
eventual exponential acceptance bound against all PPT alternatives. NPPT is
failure of positive semidefiniteness, not negative semidefiniteness. -/
theorem nppt_exponential_separation {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (hnppt : ¬ Matrix.PosSemidef (fun x y : A × B => rho (x.1,y.2) (y.1,x.2))) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : (n : ℕ) → Mat (Copies (A × B) n),
      (∀ n, 0 < n → IsEffect (T n)) ∧
      Tendsto (fun n => effectProb (1 - T n) (piKron n rho)) atTop (𝓝 0) ∧
      ∃ N : ℕ, ∀ n, N ≤ n → 0 < n → ∀ omega ∈ pptStateFamily n,
        effectProb (T n) omega ≤ (2 : ℝ) ^ (-c * n) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
