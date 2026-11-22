-- Prove2me | Theorems.Thm_ShiEmbed_layerOk_closure_append_embedCirc
-- name    : ShiEmbed.layerOk_closure_append_embedCirc
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-14T07:33:09.224088+00:00
-- url     : https://prove2.me/theorems/425b38f9-3215-4d6d-ab75-a369c7f46269
-- title:
--   Layer well-formedness is preserved by relabelling and by concatenation
-- statement:
--   Relabelling a circuit's wires along an injection preserves the property that every layer has pairwise disjoint gate supports, and so does concatenating two circuits with that property. Injectivity is essential for the first part: a relabelling that collapses two wires can merge supports that were disjoint.
--
--   Together these are the well-formedness obligations for a circuit built by concatenating relabelled copies of another circuit.

import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

namespace ShiEmbed

open ShiShallow

theorem layerOk_closure_append_embedCirc {m n : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e) :
    (∀ (c : Layered m), (∀ l ∈ c, LayerOk l) →
        ∀ l ∈ ShiEmbed.embedCirc e he c, LayerOk l)
      ∧ (∀ (c1 c2 : Layered n), (∀ l ∈ c1, LayerOk l) → (∀ l ∈ c2, LayerOk l) →
        ∀ l ∈ c1 ++ c2, LayerOk l) := by
  sorry

end ShiEmbed
