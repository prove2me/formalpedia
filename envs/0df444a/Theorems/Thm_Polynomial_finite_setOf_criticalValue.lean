-- Prove2me | Theorems.Thm_Polynomial_finite_setOf_criticalValue
-- name    : Polynomial.finite_setOf_criticalValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/807833ca-a83f-5406-b936-1b9d32ef6800
-- title:
--   Finiteness of the critical values of a polynomial
-- statement:
--   Let $k$ be a field (no assumptions of algebraic closure, perfection or characteristic are made) and let $P \in k[X]$ be a polynomial whose formal derivative `derivative P` is not the zero polynomial. The assertion is that the subset of $k$ consisting of those $c$ for which there exists some $x \in k$ with $P(x) = c$ and $P'(x) = 0$ — that is, the set of values taken by $P$ at the $k$-rational zeros of its derivative, the critical values of $P$ attained over $k$ — is a finite set in the sense of `Set.Finite`. Note that only points $x$ rational over $k$ are considered, so the set in question is the image under evaluation of $P$ of the $k$-points of the critical locus, and nothing is claimed about critical values arising from points of $P'$ over an extension of $k$.
--
--   This is the elementary statement that a polynomial map $\mathbb{A}^1 \to \mathbb{A}^1$ with non-vanishing derivative has only finitely many branch (critical) values, so that all but finitely many level sets $P = c$ are reduced. It is used in the construction of finite étale level sets on a fibre of the Deligne–Rapoport model, via [`ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self`](thm.html#ModularCurve.HpoolLevelRing.exists_finite_etale_levelRing_self).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_finite_setOf_criticalValue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

universe u

theorem Polynomial.finite_setOf_criticalValue
    {k : Type u} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite := by sorry
