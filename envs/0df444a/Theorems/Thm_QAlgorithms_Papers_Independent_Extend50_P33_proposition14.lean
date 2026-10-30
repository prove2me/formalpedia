-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition14
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:00:07.070982+00:00
-- url     : https://prove2.me/theorems/e2453b30-0288-4c69-9aec-8302caae19d9
-- title:
--   Proposition 14: conjugacy covariance and constant block traces
-- statement:
--   Let $R$ be an arbitrary unitary realization of the irreducible representation $\mu$ of $S_q$, where $q\ge1$. Let $\alpha\nearrow\mu$ denote all predecessor diagrams of size $q-1$, without a physical height restriction. Let $P_\alpha$ be the subgroup character projector and $C_\lambda$ the scalar of the sum of all transpositions in the irrep $\lambda$ (zero for an empty class). For $\pi\in S_{q-1}$ and $a<q$, let $T_a=R((a,q))$ and $A=R(\pi)$. Every predecessor compression satisfies
--
--   $$A(P_\alpha T_aP_\alpha)A^*=P_\alpha T_{\pi(a)}P_\alpha,\qquad\operatorname{Tr}(P_\alpha T_aP_\alpha)=\operatorname{Tr}(P_\alpha T_{\pi(a)}P_\alpha).$$
--
--   In a partially reduced orthonormal basis these are exactly the diagonal-block covariance and common transposition-trace identities.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 18, Proposition 14: conjugacy covariance and constant block traces

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF p.18 Proposition14, Eqs.(45)–(46): diagonal blocks expressed
basis-independently as compression by the actual subgroup projector. -/
theorem proposition14 {r D : ℕ} (mu : Schur.Partition (r+1) (r+1))
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ)
    (hR : RealizesSpechtIrrep mu R) (a : Preds mu) (pi : Equiv.Perm (Fin r)) (b : Fin r) :
    let P := subgroupProjector R a.val
    let A := (R (extendPerm pi) : Matrix (Fin D) (Fin D) ℂ)
    let T := (R (Equiv.swap b.castSucc (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ)
    let U := (R (Equiv.swap (pi b).castSucc (Fin.last r)) : Matrix (Fin D) (Fin D) ℂ)
    A * (P * T * P) * star A = P * U * P ∧
      (P * T * P).trace = (P * U * P).trace := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
