-- Prove2me | Theorems.Thm_PctDistortion_theorem_3
-- name    : PctDistortion.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:11.24683+00:00
-- url     : https://prove2.me/theorems/17449ead-2498-4096-8db9-13eaea12c91a
-- title:
--   Theorem 3 — $\inf_{G\in\mathcal H}\nu(\mathcal G^{ABC}_G)=1-2\delta^-(\mathcal H)$ for classes closed under extensions
-- statement:
--   Let $\mathcal H$ be a class of digraphs closed under extensions, and let
--   $$\delta^-(\mathcal H)=\sup_{G=(V,E)\in\mathcal H}\frac{\delta^-(G)}{|V|}$$
--   be its minimum normalized in-degree (1). Then
--   $$\inf_{G\in\mathcal H}\nu(\mathcal G^{ABC}_G)=1-2\,\delta^-(\mathcal H).$$
--   Applied to $M_\alpha$ it turns the degree condition of Theorem B into a lower bound on all ABC values, and its failure into α-majority digraphs of small value.
--
--   **Formalization Note** The supremum and infimum are stated as order predicates: if $\delta$ is the least upper bound of $\{\delta^-(G)/|V|: G\in\mathcal H\}$, then $1-2\delta$ is the greatest lower bound of $\{\nu(\mathcal G^{ABC}_G):G\in\mathcal H\}$. For an empty class no least upper bound exists in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: inf_{G∈𝓗} ν = 1 − 2 sup_{G∈𝓗} δ⁻(G)/|V| → IsLUB {δ⁻(G)/|V|} δ → IsGLB {ν(G)} (1 − 2δ); reason: avoids the junk value of a real sSup/sInf of an empty set; for a nonempty class both sides exist (the sets are bounded) and the statements agree
--   - encoding: "a set of digraphs" (all digraphs simple, §2.2) → a predicate on digraphs over finite node types whose members are nonempty and loopless; reason: the paper's standing convention "All our digraphs will be simple"; digraphs have at least one node
--   - reading: "closed under extensions" → closed under extensions with k_i ≥ 1 copies of every vertex; reason: a digraph has at least one node; the proof uses only k_i(T) = ⌊T b_i⌋ + 1 ≥ 1
--   - encoding: ν = Alice's payoff under any equilibrium → Alice's maximin value (abcValue); reason: equal by the minimax theorem; the maximin value exists for every finite game
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 3, p.17 (proof pp.17–18)

import Mathlib
import Definitions.Def_PctDistortion_inDeg
import Definitions.Def_PctDistortion_composition
import Definitions.Def_PctDistortion_abcValue

set_option autoImplicit false

namespace PctDistortion

/-- **Theorem 3** (game value and minimum normalized in-degree). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 3, p.17: let `𝓗` be
a set of digraphs closed under extensions; then `inf_{G∈𝓗} ν(G^ABC_G) = 1 − 2 δ⁻(𝓗)`, where
`δ⁻(𝓗) = sup_{G∈𝓗} δ⁻(G)/|V|` is (1), p.9.

**Formalization Note.** The supremum (1) and the infimum are stated with `IsLUB`/`IsGLB`: if `δ` is
the least upper bound of `{δ⁻(G)/|V| : G ∈ 𝓗}`, then `1 − 2δ` is the greatest lower bound of
`{ν(G^ABC_G) : G ∈ 𝓗}`. Members of `𝓗` are digraphs on finite nonempty node types without loops
(the paper's standing convention, §2.2: "All our digraphs will be simple"). For an empty class no
least upper bound exists in `ℝ` and the statement is vacuous, as the printed one is meaningless. -/
theorem theorem_3 (𝓗 : DigraphClass)
    (h𝓗 : ∀ (W : Type) [Fintype W] (G : Digraph W), 𝓗 W G → Nonempty W ∧ IsSimple G)
    (hext : ClosedUnderExtensions 𝓗) (δ : ℝ)
    (hδ : IsLUB {x : ℝ | ∃ (W : Type) (_ : Fintype W) (G : Digraph W), 𝓗 W G ∧ x = normMinInDeg G}
      δ) :
    IsGLB {x : ℝ | ∃ (W : Type) (_ : Fintype W) (G : Digraph W), 𝓗 W G ∧ x = abcValue G}
      (1 - 2 * δ) := by sorry

end PctDistortion
