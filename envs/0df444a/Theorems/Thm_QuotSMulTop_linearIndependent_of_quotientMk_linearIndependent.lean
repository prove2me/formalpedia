-- Prove2me | Theorems.Thm_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent
-- name    : QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/91fbc1f0-de33-51b2-8853-426debb606d8
-- title:
--   Lifting linear independence across M → M/xM for regular x
-- statement:
--   Let $R$ be a commutative ring that is local and Noetherian, and let $M$ be an $R$-module (an additive commutative group with an $R$-module structure). Let $x \in R$ lie in the maximal ideal of $R$ and assume that $x$ is a regular element for the scalar action on $M$, i.e. $v \mapsto x \cdot v$ is injective on $M$. Let $\iota$ be a finite index type and $m : \iota \to M$ a family of elements of $M$. Write $\mathrm{QuotSMulTop}\ x\ M$ for the quotient of $M$ by the submodule $x \cdot \top$, that is $M/xM$, a module over $R$ and in particular over $R/(x)$, where $(x) = \mathrm{Ideal.span}\ \{x\}$. The hypothesis is that the family $i \mapsto \overline{m_i}$ of images of the $m_i$ in $M/xM$ is linearly independent over $R/(x)$. The conclusion is that $m$ itself is linearly independent over $R$. No finiteness hypothesis is imposed on $M$.
--
--   This is the Nakayama-type lifting of linear independence along the reduction $M \to M/xM$ by an $M$-regular parameter in the maximal ideal; it is the independence half of the step by which a basis of $M/xM$ is lifted to a basis of $M$. It is used in [`QuotSMulTop.exists_basis_lift`](thm.html#QuotSMulTop.exists_basis_lift), which supplies the freeness statements needed in the Taylor–Wiles–Kisin patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuotSMulTop_linearIndependent_of_quotientMk_linearIndependent.lean

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

theorem QuotSMulTop.linearIndependent_of_quotientMk_linearIndependent {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsLocalRing R] [IsNoetherianRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (m : ι → M) (hli : LinearIndependent (R ⧸ Ideal.span {x}) (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
    LinearIndependent R m := by sorry
