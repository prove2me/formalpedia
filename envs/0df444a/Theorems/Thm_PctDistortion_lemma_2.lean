-- Prove2me | Theorems.Thm_PctDistortion_lemma_2
-- name    : PctDistortion.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:58.73773+00:00
-- url     : https://prove2.me/theorems/603587ff-6dab-44d5-9ab4-3826559a114f
-- title:
--   Lemma 2 — conditional distributions of an equilibrium are equilibria within blocks
-- statement:
--   Throughout, the standing assumptions of §4.1 hold: $\alpha\in[1/2,1)$, $H=(V_H,E_H)\in M_\alpha$ with $\hat\nu=\nu(\mathcal G^{ABC}_H)<1-2/s$ for an integer $s\ge 3$, $r\ge 1$ is an integer, $\ell=sr+1$, $C=\vec C^{\,r}_\ell$, and $G=C[P,H,\dots,H]$ with blocks $V_0=\{c_0,c^*\}$ and $V_i$ ($i\ne0$) copies of $H$.
--
--   If $(a,b)$ is an equilibrium of the ABC game on $G$, then for each block $i$ with $\pi(a)_i>0$ and $\pi(b)_i>0$:
--
--   1. the conditional distributions $(\phi(a)_i,\phi(b)_i)$ form an equilibrium of the ABC game on the induced subdigraph $G[V_i]$;
--   2. if $a$ is supported only on uncovered nodes of $G$, then $\phi(a)_i$ is supported only on uncovered nodes of $G[V_i]$, and likewise for $b$.
--
--   This reduces the analysis of equilibria of $G$ to the reduced game on $C$.
--
--   Differences from the source:
--   - encoding: G = C[P, H, …, H] with blocks V_0 = {c₀, c*}, V_i copies of H → blowupG on Fin 2 ⊕ ({i : Fin ℓ // i ≠ 0} × V_H) with the block map; reason: a disjoint-union node type; same digraph
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 2, p.13 (proof App. E.1, p.36)

import Mathlib
import Definitions.Def_PctDistortion_alphaMajority
import Definitions.Def_PctDistortion_uncovered
import Definitions.Def_PctDistortion_abcValue
import Definitions.Def_PctDistortion_blowupG
import Definitions.Def_BlottoLP_Flow_ZeroSum

set_option autoImplicit false

namespace PctDistortion

/-- **Lemma 2** (equilibria within blocks). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Lemma 2, p.13 (proof App. E.1, p.36), under
the standing assumptions of §4.1, p.13: `H ∈ M_α` with `ν̂ = ν(G^ABC_H) < 1 − 2/s`
for an integer `s ≥ 3`, an integer `r ≥ 1`, `ℓ = s r + 1`, and `G = C[P, H, …, H]` (`blowupG`): if `(a, b)` is an equilibrium of the ABC game on `G`, then for every block `i` with
`π(a)_i > 0` and `π(b)_i > 0` the conditional distributions `(ϕ(a)_i, ϕ(b)_i)` form an equilibrium
of the ABC game on the induced subdigraph `G[V_i]`; moreover, if `a` (respectively `b`) is supported
on uncovered nodes of `G`, then `ϕ(a)_i` (respectively `ϕ(b)_i`) is supported on uncovered nodes of
`G[V_i]`. -/
theorem lemma_2 (α : ℝ) (hα₁ : 1 / 2 ≤ α) (hα₂ : α < 1) {VH : Type} [Fintype VH] [Nonempty VH]
    (H : Digraph VH) (hH : IsAlphaMajority α H) (s : ℕ) (hs : 3 ≤ s)
    (hν : abcValue H < 1 - 2 / (s : ℝ)) (r : ℕ) (hr : 1 ≤ r)
    (a b : BlowupVertex VH s r → ℝ)
    (hab : BlottoLP.Flow.IsNashEq (abcPayoff (blowupG H s r)) a b)
    (i : Fin (s * r + 1)) (ha : 0 < blockMass a i) (hb : 0 < blockMass b i) :
    BlottoLP.Flow.IsNashEq (abcPayoff (blockSub (blowupG H s r) i)) (condDist a i)
        (condDist b i) ∧
      ((∀ x, 0 < a x → x ∈ uncovered (blowupG H s r)) →
        ∀ y, 0 < condDist a i y → y ∈ uncovered (blockSub (blowupG H s r) i)) ∧
      ((∀ x, 0 < b x → x ∈ uncovered (blowupG H s r)) →
        ∀ y, 0 < condDist b i y → y ∈ uncovered (blockSub (blowupG H s r) i)) := by sorry

end PctDistortion
