-- Prove2me | Theorems.Thm_Valued_finite_image_v_of_isCompact_of_zero_notMem
-- name    : Valued.finite_image_v_of_isCompact_of_zero_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/fd7ecc54-b6d0-5cdc-995a-ebc6ba7d6cbf
-- title:
--   A valuation takes finitely many values on a compact set avoiding 0
-- statement:
--   Let $R$ be a division ring and $\Gamma_0$ a linearly ordered commutative group with zero, and suppose $R$ carries a `Valued` structure over $\Gamma_0$: a valuation $v : R \to \Gamma_0$ together with a topology on $R$ defined by the filter basis of balls $\{x : v(x) < \gamma\}$, $\gamma \in \Gamma_0^{\times}$. Let $C \subseteq R$ be a subset which is compact and does not contain $0$. Then the image of $C$ under the map $x \mapsto v(x)$, i.e. the set $\{v(x) : x \in C\} \subseteq \Gamma_0$, is finite. Thus a valuation takes only finitely many values on any compact subset of $R \setminus \{0\}$; both hypotheses matter, since the valuation ring itself is compact in the locally compact case but contains $0$, where $v$ is not locally constant.
--
--   A non-archimedean finiteness statement: on a compact subset of $R^{\times}$ the valuation has only finitely many 'valuation patterns'. It is used in the analytic work over the local fields $K_v$ of a number field, where it reduces a sum over a compact region of $K_v^\times$ to a finite sum indexed by the values of $v$; it is cited by the two statements on windows and sums over $S$-units in the number-field analytic package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valued_finite_image_v_of_isCompact_of_zero_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Topology in

theorem Valued.finite_image_v_of_isCompact_of_zero_notMem
    {R : Type*} [DivisionRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued R Γ₀]
    (C : Set R) (hC : IsCompact C) (h0 : (0 : R) ∉ C) :
    ((fun x : R => Valued.v x) '' C).Finite := by sorry
