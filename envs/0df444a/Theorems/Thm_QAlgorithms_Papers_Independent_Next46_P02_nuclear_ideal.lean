-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P02_nuclear_ideal
-- name    : QAlgorithms.Papers.Independent.Next46.P02.nuclear_ideal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:23:52.962814+00:00
-- url     : https://prove2.me/theorems/c723fac3-41cf-4485-82fc-e2d7936079e5
-- title:
--   The nuclear ideal estimate between four Banach spaces
-- statement:
--   Let $X,Y,V,W$ be Banach spaces over the same field $\mathbb F\in\{\mathbb R,\mathbb C\}$. Let $T:X\to Y$ be nuclear, $R:V\to X$ bounded linear and $L:Y\to W$ bounded linear. The nuclear norm is the infimum of the costs $\sum_k\|f_k\|\|y_k\|$ of absolutely norm-summable nuclear representations. Then
--
--   $$
--   LTR\in\mathcal B_N(V,W),\qquad \|LTR\|_N\le\|L\|\,\|T\|_N\,\|R\|.
--   $$
--
--   Thus nuclear maps form an operator ideal across distinct domain and codomain spaces.
-- source:
--   Trace-Class and Nuclear Operators, arXiv:2204.06954v2, PDF p. 8, §4, Corollary 4.2: nuclear operator ideal estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P02

open Filter

open scoped TensorProduct Topology

attribute [local instance] Classical.propDecidable

variable {F : Type*} [RCLike F]

section Banach

variable {X Y V W : Type*}

variable [NormedAddCommGroup X] [NormedSpace F X] [CompleteSpace X]

variable [NormedAddCommGroup Y] [NormedSpace F Y] [CompleteSpace Y]

variable [NormedAddCommGroup V] [NormedSpace F V] [CompleteSpace V]

variable [NormedAddCommGroup W] [NormedSpace F W] [CompleteSpace W]

/-- PDF p.8, Corollary 4.2: the four-space nuclear ideal estimate. -/
theorem nuclear_ideal [CompleteSpace X] [CompleteSpace Y] [CompleteSpace V] [CompleteSpace W]
    (T : X →L[F] Y) (R : V →L[F] X) (L : Y →L[F] W)
    (hT : IsNuclear T) :
    IsNuclear ((L.comp T).comp R) ∧
      banachNuclearNorm ((L.comp T).comp R) ≤ ‖L‖ * banachNuclearNorm T * ‖R‖ := by sorry

end Banach

end QAlgorithms.Papers.Independent.Next46.P02

end
