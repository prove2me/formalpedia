-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_fact21
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.fact21
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T10:04:53.813555+00:00
-- url     : https://prove2.me/theorems/b801f1dd-c7b5-4420-ac7f-a4295f4b994a
-- title:
--   Fact 21: Bell sandwich of a swap
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Let $B=B_{N,n}$ be the unnormalized Bell operator on the final port and input. For every $a\in\{1,\ldots,N\}$,
--
--   $$B\,V((a,N))\,B=\begin{cases}dB,&a=N,\\B,&a<N.\end{cases}$$
--
--   The identity-coset case is $B^2=dB$ and fixes the normalization.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 22, Fact 21: Bell sandwich of a swap

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

/-- PDF p.22 Fact21 Eq.(70), including the identity-coset factor d. -/
theorem fact21 (d k : ℕ) (hd : 2 ≤ d) (a : Fin (k+2)) :
    unnormalizedPortBell d (k+2) (Fin.last (k+1)) * portSwap d k a *
      unnormalizedPortBell d (k+2) (Fin.last (k+1)) =
      (if a = Fin.last (k+1) then (d:ℂ) else 1) •
        unnormalizedPortBell d (k+2) (Fin.last (k+1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
