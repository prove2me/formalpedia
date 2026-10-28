-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_theorem_7
-- name    : SyncPrefix.Huffman.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:55.375996+00:00
-- url     : https://prove2.me/theorems/6746990b-ddb1-4f93-bde5-1d5603e383be
-- title:
--   Theorem 7, p. 7 — the composition of synchronizing complete codes is synchronizing, with shortest absorbing pair between mℓ and 2Mℓ + 2c
-- statement:
--   Let $Y$ be a code over an alphabet $\Sigma_Y$ and $Z$ a code over $\Sigma_Z$, both synchronizing complete codes (complete codes with an absorbing pair). Assume $Z$ is finite, let $m$ and $M$ be the lengths of a shortest and a longest codeword of $Z$, and let $\beta : \Sigma_Y \to Z$ be a bijection. Let $\ell$ and $c$ be the lengths of shortest absorbing pairs of $Y$ and $Z$. Then the composition $X = Y \circ_\beta Z$ is a synchronizing complete code, and the length $\ell_X$ of a shortest absorbing pair of $X$ satisfies
--   $$m\,\ell \le \ell_X \le 2M\ell + 2c.$$
--
--   The theorem says that composition changes the alphabet of a synchronizing code while preserving the length of a shortest absorbing pair up to the factors $m$ and $2M$.
--
--   Differences from the source:
--   - encoding: codes over alphabets → codes over arbitrary types `α`, `β`; reason: the hypotheses force both to be finite (a finite complete code uses finitely many letters, and `β` is in bijection with `Z`), so no new instance arises.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 7, Theorem 7

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

/-- Theorem 7 (p. 7): the composition `X = Y ∘ Z` of two synchronizing complete codes, `Z`
finite with shortest and longest codeword lengths `m` and `M`, is synchronizing, and its
shortest absorbing pair has length between `m ℓ` and `2 M ℓ + 2 c`, where `ℓ` and `c` are the
lengths of shortest absorbing pairs of `Y` and `Z`. -/
theorem theorem_7 {α β : Type} (Y : Language β) (Z : Language α)
    (hY : IsSyncCode Y) (hZ : IsSyncCode Z) (hZfin : Set.Finite (Z : Set (List α)))
    (e : β ≃ {z // z ∈ Z}) (m M : ℕ)
    (hm : IsLeast ((fun z : List α => z.length) '' (Z : Set (List α))) m)
    (hM : IsGreatest ((fun z : List α => z.length) '' (Z : Set (List α))) M) :
    IsSyncCode (compose Y Z e) ∧ m * absorbLength Y ≤ absorbLength (compose Y Z e) ∧
      absorbLength (compose Y Z e) ≤ 2 * M * absorbLength Y + 2 * absorbLength Z := by sorry

end SyncPrefix.Huffman
