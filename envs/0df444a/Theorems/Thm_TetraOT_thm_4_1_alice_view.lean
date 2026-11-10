-- Prove2me | Theorems.Thm_TetraOT_thm_4_1_alice_view
-- name    : TetraOT.thm_4_1_alice_view
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:28.997286+00:00
-- url     : https://prove2.me/theorems/edc13d5f-12f6-4451-b9cc-ccc6a218b788
-- title:
--   In the Tetrahedral Protocol Bob's selection bit $s$ is independent of Alice's view
-- statement:
--   In the Tetrahedral Protocol, fix Alice's output $(m_0, m_1)$ and her message $M \in \{X, Y, Z\}$. Then:
--
--   1. exactly 2 of the 24 deals produce both $(m_0,m_1)$ and $M$;
--   2. of these two deals, exactly one gives Bob the selection bit $s = 0$ and exactly one gives $s = 1$;
--   3. when $\rho$ is uniform on $S_4$, Bob's selection bit $s$ is independent of Alice's view, her ordered hand $(\rho(0), \rho(1))$:
--   $$
--   \mathrm{law}\big((\rho(0),\rho(1)),\ s\big) = \mathrm{law}\big(\rho(0),\rho(1)\big) \otimes \mathrm{law}(s).
--   $$
--
--   For example, the pairs of deals $(0123, 0132)$, $(0213, 0231)$ and $(1023, 1032)$ share Alice's hand and differ in $s$. This is the privacy step against a semi-honest Alice in the proof of Theorem 4.1: what she sees carries no information about Bob's choice.
--
--   **Formalization Note** Alice is deterministic and receives no message, so her view is her ordered hand, which determines $M$ and $(m_0, m_1)$. Independence is the equality of the joint law with the product of the marginal laws, written with `PMF.bind`. Bits are Booleans with $\texttt{true}=1$.
--
--   Differences from the source:
--   - reading: "Alice's view" → her ordered hand $(\rho(0),\rho(1))$; reason: Alice receives no message and acts deterministically, so everything she sees (message, output) is a function of her hand; keeping the order is the larger view
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 4.1, proof, paragraph "First, consider Alice's view", p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable
import Definitions.Def_TetraOT_tetrahedralRun

set_option autoImplicit false

namespace TetraOT

/-- **The selection bit is independent of Alice's view** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 4.1, proof, paragraph "First,
consider Alice's view", p.3; p. = PDF page, the PDF has no printed page numbers): "Moreover, of these 6
transcripts, there is a pair of cases for each M ∈ {X, Y, Z}. For each of those pairs, one produces
s = 0 and the other produces s = 1, so s is independent of Alice's view."

Three clauses:
1. for each output `(m₀, m₁)` and each message `M`, exactly 2 permutations produce both;
2. of these two, exactly one produces `s = 0` and exactly one produces `s = 1`;
3. under the uniform deal, Bob's selection bit `s` is independent of Alice's view (her ordered hand):
   the joint law of (view, `s`) is the product of the two marginal laws.

**Formalization Note.** Alice's view is her ordered hand `(ρ(0), ρ(1))`, which determines `M` and
`(m₀, m₁)` (the paper's example pairs `(0123, 0132)`, `(0213, 0231)`, `(1023, 1032)` are the two deals
sharing a hand). `s` is `(bobOut ρ).1` with `true` = 1. Independence is written as
`law(view, s) = law(view) ⊗ law(s)` through `PMF.bind`. -/
theorem thm_4_1_alice_view :
    (∀ (m : Bool × Bool) (M : Msg),
      (Finset.univ.filter (fun ρ : Equiv.Perm (Fin 4) => aliceOut ρ = m ∧ msg ρ = M)).card = 2) ∧
    (∀ (m : Bool × Bool) (M : Msg) (b : Bool),
      (Finset.univ.filter (fun ρ : Equiv.Perm (Fin 4) =>
        aliceOut ρ = m ∧ msg ρ = M ∧ (bobOut ρ).1 = b)).card = 1) ∧
    deal.map (fun ρ => (viewA ρ, (bobOut ρ).1)) =
      (deal.map viewA).bind (fun a => (deal.map (fun ρ => (bobOut ρ).1)).map (fun b => (a, b))) := by sorry

end TetraOT
