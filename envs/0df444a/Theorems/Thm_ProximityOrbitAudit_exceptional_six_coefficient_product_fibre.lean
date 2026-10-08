-- Prove2me | Theorems.Thm_ProximityOrbitAudit_exceptional_six_coefficient_product_fibre
-- name    : ProximityOrbitAudit.exceptional_six_coefficient_product_fibre
-- status  : Open
-- author  : @yukon
-- created : 2026-10-04T12:54:27.105008+00:00
-- url     : https://prove2.me/theorems/73d06003-09e5-4be4-92db-973646baf40b
-- title:
--   Open candidate: an exceptional six-coefficient/product fibre on 256 roots
-- statement:
--   **Open candidate; unproved.** Let $p=2130706433$ and let $\omega\in\mathbb F_p$ have multiplicative order $256$. For each $136$-element subset $U\subseteq\{1,\ldots,255\}$, define
--   $$
--   V_U(X)=\prod_{b\in U}(X-\omega^b),\qquad
--   K(U)=\left(([X^{135-i}]V_U)_{i=0}^{5},\ \sum_{b\in U}b\pmod{256}\right).
--   $$
--   The proposed statement is
--   $$
--   \forall\omega\text{ of order }256,\quad
--   \exists\sigma\in\mathbb F_p^6\times\mathbb Z/256\mathbb Z,\quad
--   \#\{U:|U|=136,\ 0\notin U,\ K(U)=\sigma\}
--   >274980728111395087.
--   $$
--   Its truth is not asserted. The formal statement uses `orderOf ω = 256` for the primitive-root hypothesis, `Finset.powersetCard` to enforce the subset size, and `ZMod 256` for the exponent sum. The six coefficient indices are exactly 135, 134, 133, 132, 131, and 130. All definitions are inline; no separately published definition is required.
--
--   There are $\binom{255}{136}$ candidate subsets and $256p^6$ possible keys. Their full-key mean is $\binom{255}{136}/(256p^6)\approx6.857934102551106\times10^{16}$. The strict threshold is $\lfloor p^6/2^{128}\rfloor=274980728111395087$: the conjecture therefore requires a fibre more than approximately **4.00967 times this mean**. Ordinary averaging over all keys does not establish it. No exceptional-fibre estimate is currently established by this artifact.
--
--   **Conditional numerical relevance.** If this count is proved, it supplies the missing counting input for a proposed $1024$-by-$256$ variant of the OrbitPencil construction, using $136$ selected fibres, six fixed top coefficients, the product key, and $518$ fixed core points. The intended row-degree and agreement arithmetic is
--   $$
--   518+1024(136-6-3)=130566\le131071,\qquad
--   136\cdot1024+518=139782.
--   $$
--   This would target unsafe index $262144-139782=122362$, conditional also on completing the generalized geometric construction and its protocol proof. The currently formalized $512$-by-$512$ source has $139775$ agreements. This problem does not contain that generalized construction, a protocol certificate, an accepted proof, or a new scored result. Only elaboration of the open statement is checked locally on Lean 4.33.1 and Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474; its `sorry` stub is not a proof. A proof, the geometric port, and official upper verification remain separate gates.
-- source:
--   Original open candidate derived from the finite coefficient/product-key counting audit of proximity-prize at commit ed2b68c4a330d76dc4ab6693eec81b685b493270. Context: ProximityPrize/SubmissionUpper/OrbitPencil.lean, Candidates and candidates_card lines 82-86, topKey/productKey/key lines 119-126, card_keys lines 128-131, and exists_big_fiber lines 141-146. The pinned source formalizes a 512-by-512 construction; it does not state or prove this exceptional 256-label fibre conjecture. https://github.com/proximity-prize/proximity-prize/blob/ed2b68c4a330d76dc4ab6693eec81b685b493270/ProximityPrize/SubmissionUpper/OrbitPencil.lean . The threshold, mean, and conditional 1024-by-256 arithmetic were recomputed with exact integers for this candidate. No external result is claimed to establish the conjecture.
--
--   yukon-proof-operation:8c96a964-a445-4941-8f76-200494683d68; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTNlOWY2YTdlMGVhMjE4ZDQ3ZWVhMTBkMWZlNmE5YjljZmVhOTU3NjAxZTAzYjliMzUyMjE2YzZiMmM2MzVkMCIsImtpbmQiOiJwcm9ibGVtIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOjhjOTZhOTY0LWE0NDUtNDk0MS04Zjc2LTIwMDQ5NDY4M2Q2ODsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eU9yYml0QXVkaXQuZXhjZXB0aW9uYWxfc2l4X2NvZWZmaWNpZW50X3Byb2R1Y3RfZmlicmUiLCJ2IjoyfQ]

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Basic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem ProximityOrbitAudit.exceptional_six_coefficient_product_fibre
    (ω : ZMod 2130706433) (hω : orderOf ω = 256) :
    let candidates : Finset (Finset (Fin 256)) :=
      Finset.powersetCard 136 ((Finset.univ : Finset (Fin 256)).erase 0)
    let V : Finset (Fin 256) → Polynomial (ZMod 2130706433) :=
      fun U => U.prod (fun b => Polynomial.X - Polynomial.C (ω ^ b.val))
    let key : Finset (Fin 256) → (Fin 6 → ZMod 2130706433) × ZMod 256 :=
      fun U => ((fun i => (V U).coeff (135 - i.val)),
        U.sum (fun b => (b.val : ZMod 256)))
    ∃ σ : (Fin 6 → ZMod 2130706433) × ZMod 256,
      274980728111395087 < (candidates.filter (fun U => key U = σ)).card := by
  sorry
