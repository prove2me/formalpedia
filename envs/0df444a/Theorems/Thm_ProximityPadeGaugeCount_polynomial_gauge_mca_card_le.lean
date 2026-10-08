-- Prove2me | Theorems.Thm_ProximityPadeGaugeCount_polynomial_gauge_mca_card_le
-- name    : ProximityPadeGaugeCount.polynomial_gauge_mca_card_le
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T17:06:47.777818+00:00
-- url     : https://prove2.me/theorems/e2d5fc0a-a221-47de-a398-4feebac570d7
-- title:
--   A finite MCA count for polynomial-gauge word pairs
-- statement:
--   Let K be any field of prime characteristic p. Fix polynomials g,a,b over K with IsCoprime a b, a function c:K→K, and a degree cutoff k. Put d=max(natDegree a,natDegree b), and consider the two fixed words Y₀(x)=(g·a)(x)c(x), Y₁(x)=(g·b)(x)c(x).
--
--   For every parameter γ in a finite set Γ, suppose there is its own finite support T and polynomial P such that |T|≥k+natDegree g+d, every x∈T and c(x) is fixed by the p-power Frobenius, natDegree P<k, and P agrees with Y₀+γY₁ on T. Require literally that no pair of degree-less-than-k polynomials simultaneously fits Y₀ and Y₁ on that same T. Then
--
--   |Γ|≤d(p+1)+natDegree g+1.
--
--   Supports and candidates may vary with γ. The shared data are g,a,b,c and k. The theorem allows zero g, constant a or b, zero candidates, and node zero; its proof handles these degeneracies rather than excluding them. No finite extension degree for K is assumed. All candidate fits and nonfit conditions remain over K; an algebraic closure is used only to count auxiliary roots.
--
--   The proof separates parameters that lower the degree of a+γb (at most one) from the others. Coprimality with the Frobenius-conjugated fixed-factor expression would force simultaneous fitting and contradict MCA. Each remaining bad parameter determines a distinct root of a nonzero obstruction polynomial times the conjugate of g. The degree bound gives d(p+1)+natDegree g bad parameters. Constant moving gauges and zero g are treated separately.
--
--   This is a proved count for the explicit polynomial-gauge family. It does not assert that arbitrary benchmark word pairs, or every unresolved Padé stratum, admit this representation with the required degree and support bounds. It is not a full protocol certificate or an official numerical improvement, and no external novelty claim is made.
--
--   Relation to the [open NTT exact-support MCA target](https://prove2.me/theorems/3c79fb87-13e6-4e3a-89ab-fc7e62ea648e): this supplies a counting step for a restricted shared-word polynomial-gauge class when its degree and support bounds meet that target. A universal normal-form or classification theorem is still missing; the NTT target is not completed by this result.
-- source:
--   Original research during Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575, in the setting of https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270 . Frozen theorem ProximityPadeGaugeCount.polynomial_gauge_mca_card_le source SHA-256 3244ced9afb77d00aeca64d9bf9fd82d6e595835d1cc55a6545415580a149c29. Its six-module source closure, including the nonzero obstruction argument, was independently cold-replayed and semantically reviewed. The standalone provider proof contains these arguments over the pinned Mathlib environment. This artifact does not establish a representation theorem for arbitrary proximity benchmark inputs.
--
--   yukon-proof-operation:b84a8861-1252-4934-9604-46f170eb6596; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiM2ZmNDI1OTI2YjgzYjA1MTIxYzc4ZTY3ZjhjMDFhNTE1ZDI2Y2EzNzdlNDg4ZjEwNGYzYWVkOWQxOTdkMTVhYSIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmI4NGE4ODYxLTEyNTItNDkzNC05NjA0LTQ2ZjE3MGViNjU5NjsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVBhZGVHYXVnZUNvdW50LnBvbHlub21pYWxfZ2F1Z2VfbWNhX2NhcmRfbGUiLCJ2IjoyfQ]

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Finset.Card
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.LinearCombination

open Polynomial

theorem ProximityPadeGaugeCount.polynomial_gauge_mca_card_le {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (g a b : K[X]) (hab : IsCoprime a b) (c : K → K) (k : ℕ) (Γ : Finset K)
    (hmca : ∀ γ∈Γ, ∃ (T : Finset K) (P : K[X]),
      k+g.natDegree+max a.natDegree b.natDegree≤T.card ∧
      (∀ x∈T, x^p=x) ∧ (∀ x∈T, (c x)^p=c x) ∧
      P.natDegree<k ∧
      (∀ x∈T, P.eval x=(g*a).eval x*c x+γ*((g*b).eval x*c x)) ∧
      ¬∃ P₀ P₁ : K[X], P₀.natDegree<k ∧ P₁.natDegree<k ∧
        (∀ x∈T, P₀.eval x=(g*a).eval x*c x) ∧
        (∀ x∈T, P₁.eval x=(g*b).eval x*c x)) :
    Γ.card≤max a.natDegree b.natDegree*(p+1)+g.natDegree+1 := by
  sorry
