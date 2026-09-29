-- Prove2me | Theorems.Thm_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime
-- name    : ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/16698254-a5c1-5fbc-b359-c704fa047a38
-- title:
--   Integers coprime to p are invertible in a valuation ring over p
-- statement:
--   Let $L$ be a field and let $A$ be a valuation subring of $L$. Suppose $p$ is a natural number such that $A$ lies over $p$ in the sense of the project predicate [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), that is, the image of $p$ under the canonical map $\mathbb{N} \to L$ belongs to `A.nonunits`, the non-units of $A$ (equivalently, $v_A(p) < 1$ for the valuation $v_A$ attached to $A$). Let $n$ be a natural number with $\gcd(n,p) = 1$. Then the inverse $(n : L)^{-1}$ of the image of $n$ in $L$ lies in $A$. Note that $p$ is not assumed to be prime, nor is any hypothesis imposed on the characteristic of $L$; the coprimality is the plain statement that the natural-number gcd of $n$ and $p$ equals $1$. Since the image of $n$ itself always lies in $A$, the conclusion says exactly that $n$ maps to a unit of $A$.
--
--   This is the elementary statement that a place of a field lying above $p$ is trivial on the integers prime to $p$, so that $\mathbb{Z}_{(p)}$ is contained in the valuation ring. It is used in the construction of $A$-valued points for $p$-local data at a place of $\overline{\mathbb{Q}}$ above $p$, and is cited by [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_subsingleton`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_subsingleton).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_inv_natCast_mem_of_coprime_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime
    {L : Type*} [Field L] (A : ValuationSubring L) {p : ℕ} (hA : A.LiesOverPrime p) {n : ℕ} (hn : n.Coprime p) :
    ((n : L))⁻¹ ∈ A := by sorry
