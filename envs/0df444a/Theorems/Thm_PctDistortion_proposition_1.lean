-- Prove2me | Theorems.Thm_PctDistortion_proposition_1
-- name    : PctDistortion.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:36.065566+00:00
-- url     : https://prove2.me/theorems/c786c03e-80a3-48da-9278-f02ba3f2e1e1
-- title:
--   Proposition 1 — the ABC game has an equilibrium with Alice supported on $U(G)$
-- statement:
--   For every simple digraph $G=(V,E)$ on a finite nonempty node set, the ABC game $\mathcal G^{ABC}_G$ has a mixed Nash equilibrium $(a,b)$ with $\mathrm{supp}(a)\subseteq U(G)$.
--
--   In particular $\mathrm{ABC}(G)\ne\emptyset$, so ABCα-Maximal Lotteries is well defined on every election.
--
--   Differences from the source:
--   - encoding: "|V|" for a digraph G = (V, E) → a finite nonempty node type; reason: 1/|V| and "a vertex" presuppose |V| ≥ 1
--   - encoding: simple digraph (no self-loops, no parallel arcs) → a relation without self-loops; reason: a relation has no parallel arcs
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Proposition 1, p.11 (proof App. D.1, pp.33–34)

import Mathlib
import Definitions.Def_PctDistortion_inDeg
import Definitions.Def_PctDistortion_uncovered
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_BlottoLP_Flow_ZeroSum

set_option autoImplicit false

namespace PctDistortion

/-- **Proposition 1** (equilibria supported on the uncovered set). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Proposition 1, p.11 (proof
App. D.1, pp.33–34): for every simple digraph `G = (V, E)`, the ABC game `G^ABC_G` has a Nash
equilibrium `(a, b)` such that `supp(a) ⊆ U(G)`.

**Formalization Note.** `V` is finite and nonempty. -/
theorem proposition_1 {W : Type} [Fintype W] [Nonempty W] (G : Digraph W) (hG : IsSimple G) :
    ∃ a b : W → ℝ, BlottoLP.Flow.IsNashEq (abcPayoff G) a b ∧ ∀ w, 0 < a w → w ∈ uncovered G := by sorry

end PctDistortion
