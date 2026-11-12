-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_6_4
-- name    : RelatedSchedFPTAS796.Main.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:23.420162+00:00
-- url     : https://prove2.me/theorems/4630f718-70fe-403c-a4a2-61fb2da673ba
-- title:
--   Lemma 6.4 — $|A|>|G|/2$ implies $A+A=G$
-- statement:
--   Let $A$ be a subset of a finite abelian group $G$. If $|A|>|G|/2$, then
--   $$A+A=G.$$
--
--   Lemma 6.7 uses it to conclude that a sumset covering more than half of the residues modulo $\Lambda$, doubled, covers all of them.
--
--   Differences from the source: none.
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.19, Lemma 6.4 (proof Appendix A, p.25)

import Mathlib

set_option autoImplicit false

open Pointwise

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 6.4**, p.19 (proof Appendix A, p.25). Let `A` be a subset of a finite abelian group
`G`. If `|A| > |G|/2`, then `A + A = G`. -/
theorem lemma_6_4 {G : Type*} [AddCommGroup G] [Finite G] (A : Set G)
    (hA : (Nat.card G : ℚ) / 2 < Nat.card A) : A + A = Set.univ := by sorry

end RelatedSchedFPTAS796.Main
