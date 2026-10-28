-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_composition_decoder
-- name    : SyncPrefix.Huffman.composition_decoder
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:58.935747+00:00
-- url     : https://prove2.me/theorems/61eb0fa5-94fd-47b3-ad52-1cfc25d6afb4
-- title:
--   §5, pp. 7–8 (composition decoder) — substituting the tree of a finite maximal prefix code Z for the letters of a decoder gives a Huffman decoder for (Y ∘ Z)* with Θ(n_Y n_Z) states
-- statement:
--   Let $H_Y$ be a complete automaton with $n_Y$ states over an alphabet $\Sigma_Y$, let $Z$ be a finite maximal prefix code over a finite nonempty alphabet $\Sigma_Z$, with tree $T_Z$ of $n_Z$ vertices, and let $\beta : \Sigma_Y \to Z$ be a bijection. Let $H_X$ be the decoder obtained by hanging a copy of $T_Z$ from every state $q$ of $H_Y$: the inner vertices are new states, and the leaf $\beta(a)$ of the copy at $q$ is merged with $\delta_Y(q, a)$. Then:
--
--   1. the number $N$ of states of $H_X$ satisfies
--   $$|\Sigma_Z|\cdot N + n_Y = n_Y\, n_Z,$$
--   so $N = n_Y(n_Z - 1)/|\Sigma_Z|$, which is $\Theta(n_Y n_Z)$ for a fixed alphabet (for a binary $Z$, $N = n_Y(n_Z-1)/2$);
--   2. $H_X$ is strongly connected if $H_Y$ is, and $H_X$ is a Huffman decoder if $H_Y$ is;
--   3. for every state $r$ of $H_Y$, a word $w$ over $\Sigma_Z$ maps $r$ to itself in $H_X$ if and only if $w = \beta(y)$ for a word $y$ over $\Sigma_Y$ that maps $r$ to itself in $H_Y$.
--
--   By item 3, if $H_Y$ recognizes $Y^*$ with $r$ as initial and final state, then $H_X$ recognizes $\beta(Y^*) = (Y \circ_\beta Z)^*$. Item 3 is the decoder over the alphabet of $Z$ used in the proof of Corollary 8.
--
--   Differences from the source:
--   - generalization: "a Huffman decoder with Θ(n_Y n_Z) states" → the exact count |Σ_Z|·N + n_Y = n_Y n_Z; reason: it gives Θ(n_Y n_Z) for every fixed alphabet Σ_Z, in particular the binary one of the application.
--   - generalization: H_Y a Huffman decoder for a maximal prefix code Y → H_Y any complete automaton, with strong connectivity and the Huffman property each transferred, and item 3 for every state r; reason: specializes to the source's H_Y.
--   - reading: "a Huffman decoder recognizing the star of X = Y ∘ Z" → item 3 (returns to r in H_X are the images of returns to r in H_Y); reason: H_Y recognizes Y* with r as initial and final state.
--   - reading: Huffman decoder → strongly connected, with a state whose set of first-return words is finite; reason: the paper's setting for first-return codes (p. 3); the source's H_Y, a decoder recognizing Y*, is of this kind.
--   - encoding: the alphabet Σ_Z → a finite nonempty type; reason: alphabets are finite and nonempty, and over the empty alphabet ∅ is a degenerate maximal prefix code.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, pp. 7–8, §5 (the Huffman decoder of the composition Y ∘ Z, Figure 2)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

/-- The composition decoder (pp. 7–8). Let `δY` be a complete automaton over `β` and `Z` a finite
maximal prefix code over a finite nonempty alphabet `α`, with a bijection `e : β → Z`. The decoder obtained
by hanging a copy of the tree `T_Z` from every state:
(a) has `n_Y (n_Z − 1) / |α|` states, where `n_Y` is the number of states of `δY` and `n_Z` the
number of vertices of `T_Z`;
(b) is strongly connected if `δY` is, and is a Huffman decoder if `δY` is;
(c) for every state `r`, the words returning `r` to itself in the decoder are exactly the
substitutions `β(y)` of the words `y` returning `r` to itself in `δY` (so it recognizes the star
of `X = Y ∘ Z` when `δY` recognizes `Y∗`). -/
theorem composition_decoder {σ α β : Type} [Fintype σ] [DecidableEq σ] [Fintype α] [Nonempty α]
    [DecidableEq α] (δY : σ → β → σ) (Z : Finset (List α))
    (hZ : IsMaximalPrefixCode (lang Z)) (e : β ≃ {z // z ∈ Z}) :
    Fintype.card α * Fintype.card (DecoderState σ Z) + Fintype.card σ =
        Fintype.card σ * (allPrefixes Z).card ∧
      (StronglyConnected δY → StronglyConnected (composeDecoder δY Z e)) ∧
      (IsHuffmanDecoder δY → IsHuffmanDecoder (composeDecoder δY Z e)) ∧
      ∀ (r : σ) (w : List α), run (composeDecoder δY Z e) (rootState Z r) w = rootState Z r ↔
        ∃ y : List β, run δY r y = r ∧ w = subst e y := by sorry

end SyncPrefix.Huffman
