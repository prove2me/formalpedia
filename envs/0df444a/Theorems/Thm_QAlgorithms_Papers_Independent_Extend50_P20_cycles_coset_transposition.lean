-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_cycles_coset_transposition
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.cycles_coset_transposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:09:28.338731+00:00
-- url     : https://prove2.me/theorems/97af80f2-29ef-4d7a-89cc-6ac1a1c3c03e
-- title:
--   Cycles after the coset transposition
-- statement:
--   Let $r\ge0$, let $\pi\in S_r$, and embed $\pi$ into $S_{r+1}$ by fixing its new final point $r+1$. For $a\in\{1,\ldots,r+1\}$ set $\sigma=(a,r+1)\pi$, with the transposition applied after the embedding. Counting fixed points as cycles,
--
--   $$\ell_{r+1}(\sigma)=\ell_r(\pi)+\begin{cases}0,&a\ne r+1,\\1,&a=r+1.\end{cases}$$
--
--   For a fixed $\pi$, every non-final choice of $a$ has the same cycle count. This is the coset-representative comparison used in the recurrence; no constancy throughout a coset is asserted.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 23, Lemma 12 / Eq. (109)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Lemma 12, PDF p.23, Eq.(109), with N=r+1. Multiplication is the
transposition (a,N) after the embedding fixing N. For a fixed pi, all
non-final choices of a give the same cycle count. -/
theorem cycles_coset_transposition (r : ℕ) (pi : Equiv.Perm (Fin r)) (a : Fin (r+1)) :
    cycleCount (Equiv.swap a (Fin.last r) * fixLast pi) =
      cycleCount pi + (if a = Fin.last r then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
