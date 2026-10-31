-- Prove2me | Theorems.Thm_PickAnObject_corollary_1
-- name    : PickAnObject.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:36.267955+00:00
-- url     : https://prove2.me/theorems/f50586da-8f02-435f-8b4e-2764835064e2
-- title:
--   Corollary 1 (Haeringer–Hałaburda): recursive dominance $\iff$ strategy-proofness
-- statement:
--   Let $\varphi$ be a rule on a finite set of agents $A$ and a finite set of object types $O\ni\varnothing$. Say $\varphi$ satisfies **recursive dominance** if for every agent $a$, every profile $P$, every tuple $\gamma$ of distinct object types with set of entries $I\subseteq O$, and every preference $P^*$ that ranks the entries of $\gamma$ first, in the order of $\gamma$,
--   $$\varphi_a\bigl(\gamma\oplus P_a|_{O\setminus I},\,P_{-a}\bigr)\;R_a\;\varphi_a\bigl(P^*,\,P_{-a}\bigr),$$
--   where $\gamma\oplus P_a|_{O\setminus I}$ ranks $\gamma$ first and then the remaining object types as $P_a$ does. Then
--
--   $$\varphi \text{ satisfies recursive dominance} \iff \varphi \text{ is strategy-proof}.$$
--
--   In the proof of Theorem 2 this is how strategy-proofness is used to compare the outcomes of a truthful and a deviating agent after an arbitrary history (via Lemma 1).
--
--   Differences from the source:
--   - reading: Definition 7's "$\gamma\oplus P|_{O\setminus I}$" → $\gamma\oplus P_a|_{O\setminus I}$; reason: $P$ there is agent $a$'s own preference $P_a$ (the only preference named for $a$)
--   - encoding: a set $I\subseteq O$ and a permutation $\gamma$ of $I$ → a duplicate-free list $\gamma$ with $I$ its set of entries; reason: the same data
--   - encoding: strict preferences over $O$ → rankings $O\simeq\{0,\dots,|O|-1\}$ with $\varnothing$ as `none`; reason: Lean convention; every strict linear order arises exactly once
-- source:
--   Bó–Hakimov, arXiv:2012.01025v4, App. A, Corollary 1, p.44 (with Definition 7, p.44, and the notation 𝒫|γ, P|I of p.43)

import Mathlib
import Definitions.Def_PickAnObject_Model

namespace PickAnObject

/-- **Corollary 1** (Haeringer and Hałaburda, 2016), Bó–Hakimov, arXiv:2012.01025v4, App. A,
p.44: "A rule `φ` satisfies recursive dominance if and only if it is strategy-proof."

Recursive dominance is Definition 7 (p.44): for every agent `a`, profile `P`, duplicate-free
tuple `γ` and preference `P* ∈ 𝒫|_γ`,
`φ_a(γ ⊕ P_a|_{O∖I}, P_{−a}) R_a φ_a(P*, P_{−a})`, where `I` is the set of entries of `γ`.

**Formalization Note.** `(I, γ)` is a duplicate-free list; `P|_{O∖I}` is read as `P_a|_{O∖I}`
(see `RecursiveDominance`). -/
theorem corollary_1 {A Obj : Type*} [DecidableEq A] [Fintype Obj] [DecidableEq Obj]
    (φ : Rule A Obj) :
    RecursiveDominance φ ↔ IsStrategyProof φ := by sorry

end PickAnObject
