-- Prove2me | Theorems.Thm_PctDistortion_lemma_5
-- name    : PctDistortion.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:00.740215+00:00
-- url     : https://prove2.me/theorems/0be91830-f92e-4b26-ba07-0f5e05a25424
-- title:
--   Lemma 5 — for large $r$ the value of $G$ is below $1-2/s$
-- statement:
--   Let $\alpha\in[1/2,1)$, $H\in M_\alpha$ and $s\ge3$ an integer. If $\hat\nu=\nu(\mathcal G^{ABC}_H)<1-2/s$, then there is $R$ such that for every $r\ge R$ the composed digraph $G=C[P,H,\dots,H]$ with $\ell=sr+1$ satisfies
--   $$\nu(\mathcal G^{ABC}_G)<1-\frac2s.$$
--
--   Differences from the source:
--   - reading: "there exists a sufficiently large r" → ∃ R, ∀ r ≥ R; reason: the proof shows the property for all large r (the quantity tends to its limit); the reading ∃ r alone would be weaker
--   - encoding: G = C[P, H, …, H] with blocks V_0 = {c₀, c*}, V_i copies of H → blowupG on Fin 2 ⊕ ({i : Fin ℓ // i ≠ 0} × V_H) with the block map; reason: a disjoint-union node type; same digraph
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 5, p.15 (proof pp.15–16)

import Mathlib
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_blowupG

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 5** (the composed game value drops below `1 − 2/s`). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 5, p.15 (proof
pp.15–16): if `ν̂ < 1 − 2/s`, then there exists a sufficiently large `r` such that for the
corresponding digraph `G = C[P, H, …, H]`, `ν(G^ABC_G) < 1 − 2/s`.

**Formalization Note.** Under the standing assumptions of §4.1 (`H ∈ M_α`, integer `s ≥ 3`).
"Sufficiently large `r`" is read as "for all `r ≥ R`". -/
theorem lemma_5 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {VH : Type} [Fintype VH] [Nonempty VH]
    (H : Digraph VH) (hH : IsAlphaMajority α H) (s : ℕ) (hs : 3 ≤ s)
    (hν : abcValue H < 1 - 2 / (s : ℝ)) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → abcValue (blowupG H s r) < 1 - 2 / (s : ℝ) := by sorry

end PctDistortion
