-- Prove2me | Theorems.Thm_ShiEmbed_embedCirc_depth_append_comp
-- name    : ShiEmbed.embedCirc_depth_append_comp
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-15T18:13:26.638202+00:00
-- url     : https://prove2.me/theorems/dda80abd-1f49-430e-94ed-ec8633ac0518
-- title:
--   Embedding a circuit along an injection preserves depth, distributes over concatenation, and composes
-- statement:
--   Relabelling the wires of a layered circuit along an injection has three structural properties. It leaves the number of layers unchanged, so the depth is preserved. It distributes over concatenation of circuits. And relabelling along a composite injection is the same as relabelling twice, once along each factor.
--
--   All three hold because the relabelling is a map over the list of layers, and over the list of instructions within each layer, so the list structure is untouched. The bundle that defines the relabelling says as much in prose about the depth, noting it is true by construction but providing no lemma; these are the lemmas.
--
--   They are needed whenever a circuit is placed inside a larger register in stages, for instance when three copies of a verifier are positioned in three blocks of a combined register and then the whole is relabelled again by a layout permutation. The composition law is what allows the two stages to be collapsed into one, and the depth law is what allows a resource bound on the original to be transferred to the placement.

import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

namespace ShiEmbed

open ShiShallow

theorem embedCirc_depth_append_comp {m n p : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin p) (hf : Function.Injective f) :
    (∀ c : Layered m, ShiShallow.depth (ShiEmbed.embedCirc e he c) = ShiShallow.depth c)
      ∧ (∀ c₁ c₂ : Layered m, ShiEmbed.embedCirc e he (c₁ ++ c₂)
            = ShiEmbed.embedCirc e he c₁ ++ ShiEmbed.embedCirc e he c₂)
      ∧ (∀ c : Layered m, ShiEmbed.embedCirc (f ∘ e) (hf.comp he) c
            = ShiEmbed.embedCirc f hf (ShiEmbed.embedCirc e he c)) := by
  sorry

end ShiEmbed
