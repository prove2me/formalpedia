-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_transposition_class_sum
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.transposition_class_sum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:40:03.919705+00:00
-- url     : https://prove2.me/theorems/b3f9f712-7bc9-43de-a2f7-b1d156553436
-- title:
--   Theorem 3.35(a): symmetric-group transposition class sum
-- statement:
--   For $n\ge0$, let $\kappa_n$ be the sum of all transpositions in $\mathbb C[S_n]$. For a partition $\lambda$ of $n$, let $S^\lambda$ be its Specht module and let $c(i,j)=j-i$ be box content. Then
--
--   $$\kappa_n a=a\kappa_n\quad(a\in\mathbb C[S_n]),\qquad
--   \kappa_n|_{S^\lambda}=\left(\sum_{b\in\lambda}c(b)\right)\operatorname{Id}_{S^\lambda}.$$
--
--   The Specht module is the actual Young left ideal supplied by the accepted definition layer. These scalars connect symmetric-group class sums to the central partition elements.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 27, Theorem 3.35(a): symmetric-group transposition class sum

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Transposition class sum: centrality and its scalar on every Specht module,
PDF pp.25,27, Theorem 3.35(a). The accepted Specht left ideal is used directly;
the auxiliary height bound ranges freely and therefore excludes no partition. -/
theorem transposition_class_sum (n : ℕ) :
    (∀ a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)), transpositionSum n * a = a * transpositionSum n) ∧
    (∀ (d : ℕ) (lam : QAlgorithms.Schur.Partition d n),
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        QAlgorithms.Schur.spechtRepresentation lam (Equiv.swap i j)) =
        contentSum lam.val • (LinearMap.id : Module.End ℂ (QAlgorithms.Schur.spechtSpace lam))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
