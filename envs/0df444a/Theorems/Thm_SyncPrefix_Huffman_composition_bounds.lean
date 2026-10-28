-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_composition_bounds
-- name    : SyncPrefix.Huffman.composition_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:41.935339+00:00
-- url     : https://prove2.me/theorems/463096e0-44f1-401b-9684-20bd5434b3f9
-- title:
--   Proof of Corollary 8, p. 8 — composing with a finite maximal prefix code multiplies the shortest synchronizing length by a factor between m and M, plus an additive term
-- statement:
--   Let $H_Y$ be a synchronizing complete automaton over $\Sigma_Y$ whose shortest synchronizing word has length $\ell$. Let $Z$ be a finite maximal prefix code over $\Sigma_Z$ with shortest and longest codeword lengths $m$ and $M$, let $\beta : \Sigma_Y \to Z$ be a bijection, and let $w_Z$ be a word over $\Sigma_Z$ with $\Sigma_Z^*\, w_Z \subseteq Z^*$ (a synchronizing word of $Z$). Let $H_X$ be the composition decoder (the tree of $Z$ substituted for the transitions of $H_Y$). Then $H_X$ is synchronizing, and the length $\ell_X$ of its shortest synchronizing word satisfies
--   $$m\,\ell \le \ell_X \le M\,\ell + |w_Z|.$$
--
--   For the Wielandt code $Z_L$ ($m = L$, $M = L + 1$, $|w_Z| \le L^2$) this gives $L\ell \le \ell_X \le (L+1)\ell + L^2$, which contains the bracket $\ell \log k \le \ell_X \le 2(\log k + 1)\ell + \Theta((\log k)^2)$ printed in the proof of Corollary 8 with $L = \log k$. The proof cites Theorem 7, which is about absorbing pairs of codes rather than synchronizing words of decoders; the statement here is the decoder version the argument needs.
--
--   Differences from the source:
--   - generalization: the bracket ℓ log k ≤ ℓ_X ≤ 2(log k + 1)ℓ + Θ((log k)²) for the code Z of the proof → m ℓ ≤ ℓ_X ≤ M ℓ + |w_Z| for every finite maximal prefix code Z and every w_Z with Σ*w_Z ⊆ Z*; reason: with Z = Z_L (m = L, M = L + 1, |w_Z| ≤ L²) it implies the printed bracket.
--   - generalization: the original automaton, a synchronizing Huffman decoder obtained from Corollary 6 (iii) → any synchronizing complete automaton δY on any state type; reason: the Huffman property is not used by the bracket, and the source's decoder is an instance.
--   - encoding: "the result of the composition" → the decoder `composeDecoder` of the composition (pp. 7–8); reason: the object the proof composes.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8 (second paragraph)

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

open Computability

/-- The composition bounds of the proof of Corollary 8 (p. 8), in decoder form. Let `δY` be a
synchronizing complete automaton over `β`, `Z` a finite maximal prefix code over `α` with
shortest and longest codeword lengths `m` and `M`, `e : β → Z` a bijection, and `w_Z` a word
with `u w_Z ∈ Z∗` for every word `u`. Then the composition decoder is synchronizing and
`m ℓ ≤ ℓ_X ≤ M ℓ + |w_Z|`, where `ℓ` and `ℓ_X` are the lengths of shortest synchronizing words of
`δY` and of the decoder. -/
theorem composition_bounds {σ α β : Type} [DecidableEq α] (δY : σ → β → σ)
    (Z : Finset (List α)) (hZ : IsMaximalPrefixCode (lang Z)) (e : β ≃ {z // z ∈ Z})
    (m M : ℕ) (hm : IsLeast ((fun z : List α => z.length) '' (Z : Set (List α))) m)
    (hM : IsGreatest ((fun z : List α => z.length) '' (Z : Set (List α))) M)
    (wZ : List α) (hwZ : ∀ u : List α, u ++ wZ ∈ (lang Z)∗) (hY : IsSynchronizing δY) :
    IsSynchronizing (composeDecoder δY Z e) ∧
      m * syncLength δY ≤ syncLength (composeDecoder δY Z e) ∧
      syncLength (composeDecoder δY Z e) ≤ M * syncLength δY + wZ.length := by sorry

end SyncPrefix.Huffman
