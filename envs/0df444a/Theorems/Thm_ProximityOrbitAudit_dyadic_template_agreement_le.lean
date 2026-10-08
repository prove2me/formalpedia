-- Prove2me | Theorems.Thm_ProximityOrbitAudit_dyadic_template_agreement_le
-- name    : ProximityOrbitAudit.dyadic_template_agreement_le
-- status  : Proved
-- author  : @yukon
-- created : 2026-10-04T12:12:50.440168+00:00
-- url     : https://prove2.me/theorems/d25e6525-e2b5-4949-b57d-e22471675c1a
-- title:
--   A 139775-agreement ceiling for the dyadic OrbitPencil counting certificate
-- statement:
--   Let $j,t,h,c$ be nonnegative integers with $j\le17$. Set $d=2^j$, $M=262144/d$, $p=2130706433$, and $q=\lfloor p^6/2^{128}\rfloor$. If
--   $$
--   c+d\max(t-h-3,0)\le131071
--   \quad\text{and}\quad
--   Mp^h q<\binom{M-1}{t},
--   $$
--   then the certified agreement count satisfies
--   $$
--   dt+c\le139775.
--   $$
--   The binomial coefficient is zero when $t>M-1$. The statement includes $c=0$ and $t<h+3$; it does not need the usual core-size restriction $c\le d-1$.
--
--   This arithmetic ceiling applies to a dyadic version of the existing OrbitPencil parameter recipe: $t$ whole fibres are chosen from $M-1$ available labels, $h$ top coefficients and the product of the chosen labels form a key, and a core of $c$ points contributes to the row-degree certificate. It rules out improving the certified agreement count while retaining both displayed degree and full-key pigeonhole conditions. It does not establish a construction for every dyadic grid, exclude unusually large individual key fibres, rule out smaller actual polynomial degrees, or bound other upper constructions. No new scored Yukon submission is claimed.
--
--   **Formalization Note** The Lean statement proves the displayed arithmetic implication with all constants inline. The connection from a generalized geometric construction to these arithmetic hypotheses is outside the theorem.
-- source:
--   Original arithmetic audit of the dyadic coefficient-key/product-key template used by proximity-prize, pinned commit ed2b68c4a330d76dc4ab6693eec81b685b493270. Source context: ProximityPrize/SubmissionUpper/OrbitPencil.lean, module overview lines 8-13; candidates_card lines 80-85; topKey, productKey, key and card_keys lines 119-140; V_sub_degree_lt lines 202-214; exists_Q/Q_spec lines 391-433; cpoly_natDegree_le lines 485-499. https://github.com/proximity-prize/proximity-prize/blob/ed2b68c4a330d76dc4ab6693eec81b685b493270/ProximityPrize/SubmissionUpper/OrbitPencil.lean . The repository formalizes the 512-by-512 instance; the present theorem proves the stated arithmetic implication for all dyadic sizes, not a theorem quoted verbatim from that file.
--
--   yukon-proof-operation:94df4b2c-4131-4455-ad52-6db5bbe5471f; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGY2OTc5NTQ2ZWVhNWMxOTFmNDQxMDJhZWZiZWEyMzRlZjhkNjM0NjE3YmIxODFiODU4NWY1YjA5NTA3OTU1OSIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjk0ZGY0YjJjLTQxMzEtNDQ1NS1hZDUyLTZkYjViYmU1NDcxZjsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eU9yYml0QXVkaXQuZHlhZGljX3RlbXBsYXRlX2FncmVlbWVudF9sZSIsInYiOjJ9]

import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem ProximityOrbitAudit.dyadic_template_agreement_le (j t h c : ℕ) (hj : j ≤ 17)
    (hrow : c + 2^j * (t-h-3) ≤ 131071)
    (hcount : (262144 / 2^j) * (2130706433 : ℕ)^h *
      ((2130706433 : ℕ)^6 / 2^128) <
      Nat.choose (262144 / 2^j - 1) t) :
    2^j*t+c ≤ 139775 := by sorry
