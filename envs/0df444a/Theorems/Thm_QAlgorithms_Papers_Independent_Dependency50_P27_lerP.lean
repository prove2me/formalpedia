-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_lerP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.lerP
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:43:43.730612+00:00
-- url     : https://prove2.me/theorems/b6dfcba9-541a-457c-a548-1f012e033951
-- title:
--   §3.2, Lemma lerP
-- statement:
--   Let $R$ be a discrete totally ordered integral domain, with order compatible with its ring operations. For $x,y\in R$, the indexed comparison view $L(x,y;b_1,b_2)$ has constructors from $x\le y$ at $(b_1,b_2)=(\mathrm{true},\mathrm{false})$ and from $y<x$ at $(\mathrm{false},\mathrm{true})$. The simultaneous Boolean comparisons satisfy
--
--   $$L(x,y;[x\le y],[y<x]).$$
--
--   This supplies the source's dependent two-branch comparison view. At equality the first constructor applies.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 13, §3.2, Lemma lerP

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 13, lerP, with the displayed constructor indices. -/
theorem lerP {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (x y : R) :
    LerXorGtr x y (decide (x ≤ y)) (decide (y < x)) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
