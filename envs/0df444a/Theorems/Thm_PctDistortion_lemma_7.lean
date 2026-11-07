-- Prove2me | Theorems.Thm_PctDistortion_lemma_7
-- name    : PctDistortion.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:55.870516+00:00
-- url     : https://prove2.me/theorems/79f0a2ee-027a-4f21-9951-c2256b13ba80
-- title:
--   Lemma 7 — an election implementing $G$ with percentile costs (5)
-- statement:
--   Let $s\ge3$ be an integer and $\frac{s-1}{s+1}<\alpha<\frac{s}{s+1}$; let $H\in M_\alpha$ with $\nu(\mathcal G^{ABC}_H)<1-2/s$ (§4.1). For every integer $r\ge1$, let $G=C[P,H,\dots,H]$ with $\ell=sr+1$, blocks $V_i$ and $V_0=\{c_0,c^*\}$. There exist an election $\mathcal E$ with candidate set $\mathcal C=V_G$ and a consistent metric $d\sim\vec\succ$ such that $G^\alpha_{\mathcal E}=G$ and
--   $$\mathrm{cost}^\alpha_d(c)=\begin{cases}1&c=c^*,\\3&c=c_0,\\5&c\in V_i,\ 1\le i\le r,\\3&c\in V_i,\ i>r.\end{cases}\tag{5}$$
--
--   Differences from the source:
--   - reading: "for some integer s ≥ 3" (§4.1) with no stated relation between s and α → (s − 1)/(s + 1) < α < s/(s + 1); reason: the relation the proof uses (p.39: "Because (s−1)/(s+1) < α < s/(s+1)"); it holds for s = ⌊1/(1 − α)⌋, the s of Theorem 2, and without some such relation the lemma is false (for α close to 1 the (s + 1)-voter election has no arcs)
--   - encoding: finite elections with n voters and m candidates → finite nonempty voter and candidate types; reason: the percentile cost and the lotteries presuppose n, m ≥ 1; with n = 0 the cost is undefined and with m = 0 there is no lottery
--   - encoding: G = C[P, H, …, H] with blocks V_0 = {c₀, c*}, V_i copies of H → blowupG on Fin 2 ⊕ ({i : Fin ℓ // i ≠ 0} × V_H) with the block map; reason: a disjoint-union node type; same digraph
--   - encoding: candidate equality c = c*, c = c₀ → a DecidableEq instance on V_H; reason: needed to write the case distinction; every instance is equal
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 7, p.16 (proof App. E.4, pp.38–40)

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_PctDistortion_IsMetric
import Definitions.Def_PctDistortion_percentileCost
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_blowupG

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 7** (an election implementing `G` with a high-distortion metric). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 7, p.16
(proof App. E.4, pp.38–40). For every integer `r ≥ 1`, with `G = C[P, H, …, H]` and `ℓ = s r + 1`
and `V_0 = {c₀, c*}`, there exist an election `E` with candidate set `V_G` and a metric `d ∼ ≻⃗`
such that `G^α_E = G` and (5): `cost^α_d(c) = 1` for `c = c*`, `3` for `c = c₀`, `5` for
`c ∈ V_i`, `1 ≤ i ≤ r`, and `3` for `c ∈ V_i`, `i > r`.

**Formalization Note.** Under the standing assumptions of §4.1 (`H ∈ M_α`, `ν(G^ABC_H) < 1 − 2/s`,
integer `s ≥ 3`) with `(s − 1)/(s + 1) < α < s/(s + 1)`, the relation between `α` and `s` that the
proof uses (p.39); it holds for `s = ⌊1/(1 − α)⌋`, the `s` of Theorem 2. The candidate type of `E`
is the node type of `G`, and `G^α_E = G` is equality of digraphs. -/
theorem lemma_7 (α : ℝ) (s : ℕ) (hs : 3 ≤ s) (hα₁ : ((s : ℝ) - 1) / ((s : ℝ) + 1) < α)
    (hα₂ : α < (s : ℝ) / ((s : ℝ) + 1)) {VH : Type} [Fintype VH] [Nonempty VH] [DecidableEq VH]
    (H : Digraph VH)
    (hH : IsAlphaMajority α H) (hν : abcValue H < 1 - 2 / (s : ℝ)) (r : ℕ) (hr : 1 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (E : Election V (BlowupVertex VH s r))
      (d : V → BlowupVertex VH s r → ℝ),
      IsMetric d ∧ Consistent E d ∧ alphaMajority α E = blowupG H s r ∧
        ∀ c, percentileCost α d c =
          if c = cStar then 1 else if c = c0 then 3 else if (block c).val ≤ r then 5 else 3 := by sorry

end PctDistortion
