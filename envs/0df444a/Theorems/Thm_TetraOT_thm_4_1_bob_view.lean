-- Prove2me | Theorems.Thm_TetraOT_thm_4_1_bob_view
-- name    : TetraOT.thm_4_1_bob_view
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:03.356794+00:00
-- url     : https://prove2.me/theorems/42647d07-ad60-41e0-bf23-45f4fb23112a
-- title:
--   In the Tetrahedral Protocol the unselected bit $m_{s'}$ is independent of Bob's view
-- statement:
--   In the Tetrahedral Protocol, Bob's view is the pair $(\rho(2), M)$ of his card and Alice's message, and the bit he does not learn is $m_{s'}$ with $s' = 1 - s$. Then:
--
--   1. each of the $3 \cdot 4 = 12$ Bob views $(M, \rho(2))$ is produced by exactly 2 of the 24 deals;
--   2. any two distinct deals producing the same Bob view give the same selection bit $s$ and different values of $m_{s'}$ (one gives $m_{s'} = 0$, the other $m_{s'} = 1$);
--   3. when $\rho$ is uniform on $S_4$, $m_{s'}$ is independent of Bob's view:
--   $$
--   \mathrm{law}\big((\rho(2), M),\ m_{s'}\big) = \mathrm{law}\big(\rho(2), M\big) \otimes \mathrm{law}(m_{s'}).
--   $$
--
--   Fig. 6 of the paper tabulates the two deals for each of the 12 views. This is the privacy step against a semi-honest Bob in the proof of Theorem 4.1: what he sees carries no information about the bit he did not choose.
--
--   **Formalization Note** $m_{s'}$ is $m_0$ when $s = 1$ and $m_1$ when $s = 0$. Independence is the equality of the joint law with the product of the marginal laws, written with `PMF.bind`. That the two deals of a view share $s$ is stated on p.4 ("there is one value of $s$ for which both transcripts produce the same $m_s$").
--
--   Differences from the source:
--   - encoding: $m_{s'}$ with $s' = 1 - s$ → `unchosen ρ`, defined as `if s then m₀ else m₁`; reason: the same bit, with $s$ a Boolean ($\texttt{true}=1$)
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Theorem 4.1, proof, paragraph "Next, consider Bob's view", p.3, with Fig. 6 and the following paragraph, p.4 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable
import Definitions.Def_TetraOT_tetrahedralRun

set_option autoImplicit false

namespace TetraOT

/-- **The unselected bit is independent of Bob's view** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Theorem 4.1, proof, paragraph "Next,
consider Bob's view", p.3, with Fig. 6 and the paragraph after it, p.4; p. = PDF page, the PDF has no
printed page numbers): "Next, consider Bob's view, produced by a particular M and ρ(2). There are 12
cases, and in each case, there is a pair of transcripts producing it. Let s′ = 1−s. For each such pair,
one produces m_{s′} = 0 and the other produces m_{s′} = 1, so m_{s′} is independent of Bob's view."
and (p.4) "For any M ∈ {X, Y, Z} and hand ρ(2), there are precisely 2 transcripts. By inspection, there
is one value of s for which both transcripts produce the same m_s, and an opposite value s′ for which
the transcripts produce different m_{s′}."

Three clauses:
1. for each of the 12 Bob views `(M, ρ(2))`, exactly 2 permutations produce it;
2. any two distinct permutations producing the same Bob view give the same `s` and different
   `m_{s′}`;
3. under the uniform deal, `m_{s′}` is independent of Bob's view `(ρ(2), M)`: the joint law of
   (view, `m_{s′}`) is the product of the two marginal laws.

**Formalization Note.** `unchosen ρ` is `m_{s′}` (`m₀` when `s = 1`, `m₁` when `s = 0`). Bob's view is
`viewB ρ = (ρ(2), M)`. Independence is written as `law(view, m_{s′}) = law(view) ⊗ law(m_{s′})`
through `PMF.bind`. -/
theorem thm_4_1_bob_view :
    (∀ (M : Msg) (c : Fin 4),
      (Finset.univ.filter (fun ρ : Equiv.Perm (Fin 4) => msg ρ = M ∧ ρ 2 = c)).card = 2) ∧
    (∀ ρ ρ' : Equiv.Perm (Fin 4), ρ ≠ ρ' → viewB ρ = viewB ρ' →
      (bobOut ρ).1 = (bobOut ρ').1 ∧ unchosen ρ ≠ unchosen ρ') ∧
    deal.map (fun ρ => (viewB ρ, unchosen ρ)) =
      (deal.map viewB).bind (fun w => (deal.map unchosen).map (fun b => (w, b))) := by sorry

end TetraOT
