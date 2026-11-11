-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_lemma_5_1
-- name    : RandomColorMix269.Mixing.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:42.177267+00:00
-- url     : https://prove2.me/theorems/f74156ef-a765-44c3-ab51-124e8d906370
-- title:
--   Lemma 5.1 — list colourings with slack $|L(x_i)|\ge\deg_{H_i}(x_i)+2$ exist and are single-site connected
-- statement:
--   Let $H$ be a finite graph with colour lists $L(x)$, and suppose its vertices admit an ordering $x_1,\dots,x_m$ such that, with $H_i=H[\{x_i,\dots,x_m\}]$,
--   $$
--   |L(x_i)|\ge\deg_{H_i}(x_i)+2\qquad\text{for every }i .
--   $$
--   Then proper list-colourings exist, and any two proper list-colourings are joined by a sequence of proper list-colourings in which consecutive colourings differ at exactly one vertex.
--
--   The lemma gives the connectivity of every conditional support used in §5 (Corollary 5.12, Proposition 5.17) and the extension property of Proposition 5.11.
--
--   Differences from the source:
--   - encoding: arbitrary finite colour lists L(x) → lists L(x) ⊆ Fin q for an arbitrary q; reason: any finite colour universe relabels into some Fin q
--   - encoding: ordering x_1,…,x_m and deg_{H_i}(x_i) → a bijection e : Fin |V| ≃ V and the number of neighbours of e(i) with index ≥ i; reason: the same quantity
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.26, Lemma 5.1

import Definitions.Def_RandomColorMix269_Mixing_Geometry

open scoped Classical BigOperators
open Finset
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Lemma 5.1, p.26, including existence. An equivalence lists every vertex once. -/
theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (H : SimpleGraph V) (L : V → Finset (Fin q)) (e : Fin (Fintype.card V) ≃ V)
    (hslack : ∀ i : Fin (Fintype.card V),
      (univ.filter fun w : V => H.Adj (e i) w ∧ i ≤ e.symm w).card + 2 ≤ (L (e i)).card) :
    (∃ x : V → Fin q, ProperListColoring H L x) ∧
      ∀ x y : V → Fin q, ProperListColoring H L x → ProperListColoring H L y →
        Relation.ReflTransGen (fun a b : V → Fin q =>
          ProperListColoring H L a ∧ ProperListColoring H L b ∧ hamming a b = 1) x y := by sorry

end RandomColorMix269.Mixing
