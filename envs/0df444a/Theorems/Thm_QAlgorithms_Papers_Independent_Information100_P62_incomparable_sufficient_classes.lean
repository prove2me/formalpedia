-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_incomparable_sufficient_classes
-- name    : QAlgorithms.Papers.Independent.Information100.P62.incomparable_sufficient_classes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:54:25.265476+00:00
-- url     : https://prove2.me/theorems/c2f857d0-6a4f-405e-a292-ebbf05377244
-- title:
--   Remark 4.23: incomparable sufficient classes
-- statement:
--   For the five-cycle stochastic channel $N(j|i)=1/2$ when $j=i$ or $j=i+1\pmod5$, the associated channel $\Phi_N$ satisfies
--   $$Q_0(\Phi_N)=0,\qquad\alpha(S_{\Phi_N})=2,\qquad\alpha(S_{\Phi_N}\otimes S_{\Phi_N})=5.$$
--   Its system is not graph-isomorphic to any finite-dimensional unital star-algebra. Conversely, for every $d\ge2$, the identity channel has an algebraic operator system and $Q_0({\rm id}_d)=\log_2d>0$. Thus the two sufficient classes are incomparable.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 43, Remark 4.23: incomparable sufficient classes

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.43, Remark 4.23: incomparable sufficient classes. -/
theorem incomparable_sufficient_classes :
    IsChannel cycleChannel ∧ quantumCapacity cycleChannel = 0 ∧
    alpha (graph cycleChannel) = 2 ∧
    alpha (graph (tensorChannel cycleChannel cycleChannel)) = 5 ∧
    (∀ d : ℕ, 0 < d → ∀ S : Submodule ℂ (Matrix (Fin d) (Fin d) ℂ),
      IsAlgebra S → ¬ GraphIso (graph cycleChannel) S) ∧
    (∀ d : ℕ, 2 ≤ d → IsAlgebra (graph (id : Superop (Fin d) (Fin d))) ∧
      quantumCapacity (id : Superop (Fin d) (Fin d)) = logTwo d ∧ 0 < logTwo d) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
