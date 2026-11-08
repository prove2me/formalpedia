-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_2_4
-- name    : PercCubeCycles.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:44.401746+00:00
-- url     : https://prove2.me/theorems/8c0fce26-6893-4596-a485-728954bbed65
-- title:
--   Lemma 2.4 — the giant has order $(2\varepsilon+O(\varepsilon^2))2^d$, expands by $1/d^2$, and other components have $<d^2$ vertices
-- statement:
--   Let $\varepsilon>0$ be sufficiently small and $p=(1+\varepsilon)/d$. Whp the giant component $L_1$ of $Q^d_p$ has order $(2\varepsilon+O(\varepsilon^2))2^d$, and for every set $S\subseteq V(L_1)$ with $|S|\le2|V(L_1)|/3$,
--   $$|N_{L_1}(S)|\ge\frac{|S|}{d^2}.$$
--   Moreover, whp the second largest component has order less than $d^2$.
--
--   This records the expansion of the giant used in the joining stage.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small, $O(\varepsilon^2)$ → $\exists K,\varepsilon_0\ \forall\varepsilon\in(0,\varepsilon_0)$, error at most $K\varepsilon^2$; reason: $K$ precedes $\varepsilon$, so it does not depend on $\varepsilon$
--   - reading: the giant component $L_1$ → every vertex set of a largest component; reason: the page assumes a unique giant; the statement for every largest component covers ties and is not the weaker reading
--   - reading: the second largest component has order less than $d^2$ → every component other than a largest $L_1$ has fewer than $d^2$ vertices; reason: equivalent, and avoids ranking
--   - encoding: two whp events ("Finally, whp …") → one conjunction under one limit; reason: the intersection of two whp events is whp
--   - encoding: $|N_{L_1}(S)|\ge|S|/d^2$ → $|S|\le d^2|N_{L_1}(S)|$ in $\mathbb N$; reason: equivalent for $d\ge1$, and whp sees only large $d$
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 2.4, p.7

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 2.4, p.7, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For small `ε > 0` and `p = (1 + ε)/d`, whp every largest component `L₁` of
`Q^d_p` has order `(2ε + O(ε²))2^d`, every `S ⊆ V(L₁)` with `|S| ≤ 2|V(L₁)|/3` has
`|N_{L₁}(S)| ≥ |S|/d²`, and every other component has fewer than `d²` vertices.

**Formalization Note.** The constant `K` of `O(ε²)` precedes `ε`. "Second largest component" is
read as every component other than a chosen largest one. The two whp events of the page are one
conjunction under one limit, which is equivalent. -/
theorem lemma_2_4 :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
        |(L₁.card : ℝ) - 2 * ε * 2 ^ d| ≤ K * ε ^ 2 * 2 ^ d ∧
        (∀ S ⊆ L₁, 3 * S.card ≤ 2 * L₁.card →
          S.card ≤ d ^ 2 * (nbhd (restrict (openGraph ω) L₁) S).card) ∧
        ∀ S, IsComponentSet (openGraph ω) S → S ≠ L₁ → S.card < d ^ 2 := by sorry

end PercCubeCycles
