-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_6_3
-- name    : PercCubeCycles.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:31.11583+00:00
-- url     : https://prove2.me/theorems/0f6d6e46-6fe4-4c98-9277-690ddf56e3db
-- title:
--   Lemma 6.3 — interior-closed trees in $C_2$ can be pruned and extended to special trees
-- statement:
--   Under the standing assumptions of §6 ($\varepsilon>0$ sufficiently small, $p=(1+\varepsilon)/d$), whp every tree $T\subseteq C_2$ with at least $d^3$ vertices that is interior-closed in $C_2$ admits trees $T^-\subseteq T\subseteq T^+\subseteq C_2$ such that
--
--   1. $|V(T^-)|\ge|V(T)|/d^3$, $\ell(T^-)=\ell(T)$, and $T^-$ is $Q^d_p$-special;
--   2. $|V(T^+)|\le d^3|V(T)|$, $\ell(T)\le\ell(T^+)\le2\ell(T)$, and $T^+$ is $Q^d_p$-special and almost interior-closed in $C_2$.
--
--   This reduces the expansion of connected sets of $C_2$ to bounds on special trees.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small → $\exists\varepsilon_0>0\ \forall\varepsilon\in(0,\varepsilon_0)$; reason: the standard meaning of the phrase
--   - reading: $C_2$: "the 2-core of the giant component" (Theorems 2, 6) and "the largest component of its 2-core" (p.17) → the 2-core of every largest component $L_1$; reason: the 2-core of a connected graph is connected, so the two wordings name one object
--   - encoding: $|V(T^-)|\ge|V(T)|/d^3$ → $|V(T)|\le d^3|V(T^-)|$; reason: equivalent for $d\ge1$, and whp sees only large $d$
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 6.3, p.20

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 6.3, p.20, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Under the standing assumptions of §6 (p.17), whp every tree `T ⊆ C₂` with at
least `d³` vertices that is interior-closed in `C₂` admits trees `T⁻ ⊆ T ⊆ T⁺ ⊆ C₂` such that
(i) `|V(T⁻)| ≥ |V(T)|/d³`, `ℓ(T⁻) = ℓ(T)`, and `T⁻` is `Q^d_p`-special;
(ii) `|V(T⁺)| ≤ d³|V(T)|`, `ℓ(T) ≤ ℓ(T⁺) ≤ 2ℓ(T)`, and `T⁺` is `Q^d_p`-special and almost
interior-closed in `C₂`.

**Formalization Note.** "`Q^d_p`-special" is `Q^d_p`-special `(a, b)` for some `a, b`. -/
theorem lemma_6_3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
        ∀ T : (coreGraph (openGraph ω) L₁).Subgraph, T.coe.IsTree → d ^ 3 ≤ T.verts.ncard →
          IsInteriorClosed (coreGraph (openGraph ω) L₁) T →
          ∃ Tm Tp : (coreGraph (openGraph ω) L₁).Subgraph, Tm ≤ T ∧ T ≤ Tp ∧
            Tm.coe.IsTree ∧ Tp.coe.IsTree ∧
            (T.verts.ncard ≤ d ^ 3 * Tm.verts.ncard ∧ leafCount Tm = leafCount T ∧
              ∃ a b, IsSpecial (openGraph ω) Tm a b) ∧
            (Tp.verts.ncard ≤ d ^ 3 * T.verts.ncard ∧
              leafCount T ≤ leafCount Tp ∧ leafCount Tp ≤ 2 * leafCount T ∧
              (∃ a b, IsSpecial (openGraph ω) Tp a b) ∧
              IsAlmostInteriorClosed (coreGraph (openGraph ω) L₁) Tp) := by sorry

end PercCubeCycles
