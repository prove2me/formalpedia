-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_subintP
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.subintP
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:44:44.185989+00:00
-- url     : https://prove2.me/theorems/64d7a2fb-480b-4f13-adaa-7fb216d78e13
-- title:
--   §3.3, Lemma subintP
-- statement:
--   Let $R$ be a discrete totally ordered integral domain, with order compatible with its ring operations. Let $I_1,I_2$ be intervals whose endpoints may be finite open, finite closed, or infinite. Let $\operatorname{subint}$ be the Boolean sufficient test comparing lower and upper endpoint constraints, respecting endpoint openness. Then
--
--   $$\operatorname{subint}(I_1,I_2)=\mathrm{true}\quad\Longrightarrow\quad \forall x\in R,\ x\in I_1\Longrightarrow x\in I_2.$$
--
--   This is soundness of the endpoint test; empty intervals need not satisfy the test.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 15, §3.3, Lemma subintP

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 15–16, subintP; only soundness is asserted. -/
theorem subintP {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (i2 i1 : Interval R)
    (h : subint i1 i2 = true) :
    ∀ x, intervalMem i1 x → intervalMem i2 x := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
