-- Prove2me | Theorems.Thm_SeqDiagnosis_BeliefRecon_row_RP_eq_beta
-- name    : SeqDiagnosis.BeliefRecon.row_RP_eq_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:59.162238+00:00
-- url     : https://prove2.me/theorems/f14b332a-ff69-41bc-97f3-21520f0f076f
-- title:
--   Proof of Theorem 1, p. ec1 — rows and exponents of the rank decomposition
-- statement:
--   Suppose $\mathbb B=\mathbb R\mathbb P$, where row $j$ of $\mathbb B$ is $\beta_j^{\mathsf T}$. Then row $j$ of $\mathbb R\mathbb P$ is $\beta_j^{\mathsf T}$, so its normalizing constant equals $\beta_{j0}$. For a nonempty observation list $y_1,\ldots,y_t$, with $x_t=\mathbb P\sum_m h(y_m)/t$,
--
--   $$t\bigl(\beta_{j0}+e_j\mathbb R x_t\bigr)=t\beta_{j0}+\beta_j^{\mathsf T}\sum_{m=1}^t h(y_m).$$
--
--   This identity connects the exponent in the reconstruction formula to the exponent in the class density model. The equality of normalizers is included explicitly because equation (3) defines its normalizer using $\mathbb R\mathbb P$.
--
--   **Formalization Note** The source's standing density assumptions are carried through, and the list is nonempty so its length can be used as a divisor.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. ec1 (PDF 38), proof of Theorem 1, first two displays

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open Matrix

namespace SeqDiagnosis.BeliefRecon

/-- A row of the rank decomposition is its tilting vector; hence the two normalizers
and the cumulative exponents agree. -/
theorem row_RP_eq_beta {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (hS : M.Standing) (hETM : M.ETM)
    (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (hRP : M.Bmat = R * P) (j : Fin N) :
    (R * P) j = M.beta j ∧
    betaZero M R P j = M.normConst (M.beta j) ∧
    ∀ ys : List Y, ys ≠ [] →
      (ys.length : ℝ) * (betaZero M R P j + (R *ᵥ diagStat M P ys) j) =
        (ys.length : ℝ) * M.normConst (M.beta j) + M.beta j ⬝ᵥ (ys.map M.h).sum := by sorry

end SeqDiagnosis.BeliefRecon
