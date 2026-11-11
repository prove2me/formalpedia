-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_lemma_4_11
-- name    : UnitaryQIPPSPACE.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:31:07.928544+00:00
-- url     : https://prove2.me/theorems/e73fb306-eb6f-442d-9e5b-1d0693b87f4c
-- title:
--   Lemma 4.11 — iterated differences
-- statement:
--   Let $m\ge1$, $j\ge0$, $g:\{0,1\}^m\to\{0,1\}$ and $a_1,\dots,a_j\in\{0,1\}^m$. With $g_0:=g$, $g_i:=\Delta_{a_i}g_{i-1}$ and $a_S:=\bigoplus_{i\in S}a_i$ ($a_\emptyset=0^m$),
--   $$g_j(x)=\bigoplus_{S\subseteq[j]}g(x\oplus a_S),$$
--   and for $j=m$ the function $g_m$ is constant.
--
--   It makes the injection recursion terminate after $m$ rounds.
--
--   Differences from the source: none.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.11, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_boolPhaseGate

namespace UnitaryQIPPSPACE

/-- **Lemma 4.11 (Iterated differences, cf. [DGH+25, Section 4.6])** (He, Ou, Zhao, *unitaryQIP =
unitaryPSPACE*, arXiv:2611.02819, held version sha256 9e357a00…, p. 27 (PDF p. 29)): "Let `m ≥ 1` and
`j ≥ 0` be integers, `g : {0,1}^m → {0,1}` be a Boolean function, and `a₁, …, a_j ∈ {0,1}^m` be
bitstrings. Define `g₀ := g` and `g_i := Δ_{a_i} g_{i−1}` for `i ∈ [j]`. For all subsets `S ⊆ [j]`,
define `a_S := ⊕_{i ∈ S} a_i` with the convention that `a_∅ := 0^m`. Then, we have
`g_j(x) = ⊕_{S ⊆ [j]} g(x ⊕ a_S)`, (18) and for `j = m`, the function `g_m` is a constant."

The XOR over `S ⊆ [j]` is `1` iff an odd number of subsets `S` have `g(x ⊕ a_S) = 1`. -/
theorem lemma_4_11 (m j : ℕ) (hm : 1 ≤ m) (g : Bits m → Bool) (a : Fin j → Bits m) :
    (∀ x : Bits m, iterDiff g (List.ofFn a) x =
      decide (Odd (Finset.univ.filter fun S : Finset (Fin j) =>
        g (Bits.xor x (xorSet a S)) = true).card)) ∧
    (j = m → ∃ c : Bool, ∀ x : Bits m, iterDiff g (List.ofFn a) x = c) := by sorry

end UnitaryQIPPSPACE
