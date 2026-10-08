-- Prove2me | Theorems.Thm_ProximityUniversalReplacementV1_no_strict_universal_replacement
-- name    : ProximityUniversalReplacementV1.no_strict_universal_replacement
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T14:25:18.970828+00:00
-- url     : https://prove2.me/theorems/e05d939e-5c46-4e67-8ae3-81fdb73e6bab
-- title:
--   Universal factors admit no strictly cheaper contact-preserving replacement
-- statement:
--   Let $\mathcal A$ be the explicitly constrained polynomial space defined by the three source bounds and local contacts in the imported definition. Assume that $\mathcal A$ contains a nonzero polynomial and that a nonzero polynomial $U$ divides every $Q\in\mathcal A$. The index set of local data may be arbitrary, and each contact multiplicity $m_i$ may differ.
--
--   Suppose a polynomial $P$ does not exceed the actual source footprints of $U$:
--   $$\operatorname{wt}_{(1,w,w-1,0)}P\le\operatorname{wt}_{(1,w,w-1,0)}U,\qquad
--   \operatorname{wt}_{(0,1,1,1)}P\le\operatorname{wt}_{(0,1,1,1)}U,\qquad
--   \deg_RP\le\deg_RU.$$
--   At every node require the clipped contact
--   $$\operatorname{ord}_i(P)\ge\min(m_i,\operatorname{ord}_i(U)),$$
--   interpreted as polynomial divisibility $T^{\min(m_i,\operatorname{ord}_i(U))}\mid\Phi_i(P)$, so that zero also satisfies it. For any nonnegative monomial-weight objective $a$, if
--   $$\operatorname{wt}_aP<\operatorname{wt}_aU,$$
--   then $P=0$.
--
--   The source comparisons use the actual degrees of $U$, not merely the outer caps $D,L,s$. Universality means divisibility over the concrete admissible space; replacement closure is proved, not assumed. Choose a nonzero admissible $Q=UV$ with minimal objective. A nonzero replacement would make $PV$ admissible with a smaller objective, a contradiction.
--
--   This result can rule out proposed universal factors once a nonzero contact-preserving replacement is independently constructed. It does not construct such a replacement, identify a universal factor for a concrete instance, prove the separate ConstraintKernel bridge, or improve a numerical proximity threshold.
-- source:
--   A standalone generalization of the actual-universal-factor replacement argument developed during research on the Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575. The polynomial/contact conventions come from https://github.com/proximity-prize/proximity-prize/blob/ed2b68c4a330d76dc4ab6693eec81b685b493270/ProximityPrize/SubmissionLower/LowerFoundation.lean and MergedInfra6815_7.lean in the same directory. The separate local ConstraintKernel-to-contact-space equivalence is not imported or claimed by this standalone theorem. No new numerical threshold or verified benchmark submission is asserted.
--
--   yukon-proof-operation:c4c4c2fb-5dee-41b7-8474-3fd770a89420; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTNkNDdiNDAxMGRmODI3MmZjNTA2NDNkN2M0N2U3NjVjYzg2ODQ3YzA4MDVhYzI5Mjg2M2JlYzE0NTBlNzg4OCIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmM0YzRjMmZiLTVkZWUtNDFiNy04NDc0LTNmZDc3MGE4OTQyMDsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVVuaXZlcnNhbFJlcGxhY2VtZW50VjEubm9fc3RyaWN0X3VuaXZlcnNhbF9yZXBsYWNlbWVudCIsInYiOjJ9]

import Definitions.Def_ProximityUniversalReplacementV1

open ProximityUniversalReplacementV1 MvPolynomial
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ProximityUniversalReplacementV1.no_strict_universal_replacement {K : Type*} [Field K] {I : Type*}
    (D w L s : ℕ) (m : I → ℕ) (nodes u0 u1 : I → K)
    (U : Poly4 K) (hU : U ≠ 0)
    (hne : ∃ Q : Poly4 K, Q ≠ 0 ∧ admissible K D w L s m nodes u0 u1 Q)
    (hdiv : ∀ Q : Poly4 K, admissible K D w L s m nodes u0 u1 Q → U ∣ Q)
    (P : Poly4 K)
    (hcontactWeight : weightedTotalDegree ![1, w, w - 1, 0] P ≤
      weightedTotalDegree ![1, w, w - 1, 0] U)
    (htotal : weightedTotalDegree ![0, 1, 1, 1] P ≤ weightedTotalDegree ![0, 1, 1, 1] U)
    (hslope : P.degreeOf 2 ≤ U.degreeOf 2)
    (objective : Fin 4 → ℕ)
    (hstrict : weightedTotalDegree objective P < weightedTotalDegree objective U)
    (hcontact : ∀ i, contactAtLeast K (nodes i) (u0 i) (u1 i)
      (min (m i) (contactOrder K (nodes i) (u0 i) (u1 i) U)) P) : P = 0 := by sorry
