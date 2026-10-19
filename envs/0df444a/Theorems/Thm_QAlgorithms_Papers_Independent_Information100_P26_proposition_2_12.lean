-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_proposition_2_12
-- name    : QAlgorithms.Papers.Independent.Information100.P26.proposition_2_12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:17:02.419414+00:00
-- url     : https://prove2.me/theorems/d3b133e8-3bcb-4130-8763-311ba5a837ce
-- title:
--   Proposition 2.12: three Choi characterizations of twisted dephasing
-- statement:
--   Let $d\ge1$ and let $\phi:M_d\to M_d$ be complex-linear. The following three conditions are equivalent:
--
--   1. $\phi$ is twisted dephasing.
--   2. There are orthonormal bases $(u_k)_{k=1}^d,(v_k)_{k=1}^d$ of $\mathbb C^d$ such that
--   $$J(\phi)=\sum_{k=1}^d |u_k\otimes v_k\rangle\langle u_k\otimes v_k|.$$
--   3. $J(\phi)$ is separable, self-adjoint and idempotent, and both partial traces equal $I_d$.
--
--   Here $J(\phi)=\sum_{ij}\phi(E_{ij})\otimes E_{ij}$ is unnormalized, with output factor first. This characterizes twisted dephasing intrinsically through its Choi matrix.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 7, Proposition 2.12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Proposition 2.12, PDF pp.7,8. The Choi-factor bases are existential; no pointwise Kraus-to-Choi formula without input conjugation is asserted. -/
theorem proposition_2_12 {d : ℕ} (hd : 0 < d) (t : Map d) :
    (Twisted t ↔ ∃ U V : Unitary d,
      choi t = ∑ k : Fin d,
        Matrix.kronecker
          (outer (fun i => U i k) (fun i => U i k))
          (outer (fun i => V i k) (fun i => V i k))) ∧
    (Twisted t ↔ QAlgorithms.Entanglement.IsSeparablePositive (choi t) ∧
      (choi t)ᴴ = choi t ∧ choi t * choi t = choi t ∧
      (fun i j => ∑ k, choi t (i,k) (j,k)) = (1 : Mat d) ∧
      QAlgorithms.traceLeft (choi t) = (1 : Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
