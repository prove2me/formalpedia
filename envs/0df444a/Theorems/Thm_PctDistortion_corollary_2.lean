-- Prove2me | Theorems.Thm_PctDistortion_corollary_2
-- name    : PctDistortion.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:26.032306+00:00
-- url     : https://prove2.me/theorems/c165d5ab-7850-4ac5-994d-4772ac62aa3b
-- title:
--   Corollary 2 — Alice's mass on blocks $1,\dots,r$ equals $(1-\nu(\mathcal G^{ABC}_G))/2$
-- statement:
--   Throughout, the standing assumptions of §4.1 hold: $\alpha\in[1/2,1)$, $H=(V_H,E_H)\in M_\alpha$ with $\hat\nu=\nu(\mathcal G^{ABC}_H)<1-2/s$ for an integer $s\ge 3$, $r\ge 1$ is an integer, $\ell=sr+1$, $C=\vec C^{\,r}_\ell$, and $G=C[P,H,\dots,H]$ with blocks $V_0=\{c_0,c^*\}$ and $V_i$ ($i\ne0$) copies of $H$.
--
--   Let $a\in\mathrm{ABC}(G)$ be an arbitrary equilibrium strategy of Alice supported only on uncovered candidates. Then $a_{c^*}=0$ and
--   $$\sum_{i=1}^r\sum_{u\in V_i}a_u=\frac{1-\nu(\mathcal G^{ABC}_G)}{2}.$$
--   With the metric of Lemma 7 this forces the expected cost of $a$ to be $4-\nu(\mathcal G^{ABC}_G)$.
--
--   Differences from the source:
--   - encoding: G = C[P, H, …, H] with blocks V_0 = {c₀, c*}, V_i copies of H → blowupG on Fin 2 ⊕ ({i : Fin ℓ // i ≠ 0} × V_H) with the block map; reason: a disjoint-union node type; same digraph
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 2, p.14 (proof p.15)

import Mathlib
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_abcMaximal
import Definitions.Def_PctDistortion_blowupG

set_option autoImplicit false

namespace PctDistortion

/-- **Corollary 2**. Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 2, p.14 (proof p.15), under the standing assumptions of §4.1, p.13: `H ∈ M_α` with `ν̂ = ν(G^ABC_H) < 1 − 2/s`
for an integer `s ≥ 3`, an integer `r ≥ 1`, `ℓ = s r + 1`, and `G = C[P, H, …, H]` (`blowupG`): every `a ∈ ABC(G)` (an
equilibrium strategy of Alice supported only on uncovered candidates) has `a_{c*} = 0` and
`Σ_{i=1}^{r} Σ_{u ∈ V_i} a_u = (1 − ν(G^ABC_G))/2`. -/
theorem corollary_2 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {VH : Type} [Fintype VH] [Nonempty VH]
    (H : Digraph VH) (hH : IsAlphaMajority α H) (s : ℕ) (hs : 3 ≤ s)
    (hν : abcValue H < 1 - 2 / (s : ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (a : BlowupVertex VH s r → ℝ) (ha : a ∈ abcMaximal (blowupG H s r)) :
    a cStar = 0 ∧
      (∑ x, if 1 ≤ (block x).val ∧ (block x).val ≤ r then a x else 0) =
        (1 - abcValue (blowupG H s r)) / 2 := by sorry

end PctDistortion
