-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_6_5
-- name    : PercCubeCycles.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:12.645954+00:00
-- url     : https://prove2.me/theorems/5e4dbd66-05ec-4205-b533-e1c3bc9a660e
-- title:
--   Lemma 6.5 — special trees in $C_2$ satisfy $b<\varepsilon^{10}s$, $a\le1000\varepsilon s$, and $a\ge\varepsilon s/1000$ if almost interior-closed
-- statement:
--   Let $\alpha=\varepsilon^{1/\varepsilon^{20}}$, $m=\varepsilon^22^{\alpha d}$, $M=\varepsilon^{-2}2^{\alpha d}$. Whp every $Q^d_p$-special $(a,b)$-tree $T\subseteq C_2$ of order $s$ with $m/d^4\le s\le Md^5$ satisfies
--   $$b<\varepsilon^{10}s,\qquad a\le1000\varepsilon s.$$
--   If in addition $T$ is almost interior-closed in $C_2$, then $a\ge\varepsilon s/1000$.
--
--   These leaf counts are the source of the constants in Theorem 6.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small → $\exists\varepsilon_0>0\ \forall\varepsilon\in(0,\varepsilon_0)$; reason: the standard meaning of the phrase
--   - reading: $C_2$: "the 2-core of the giant component" (Theorems 2, 6) and "the largest component of its 2-core" (p.17) → the 2-core of every largest component $L_1$; reason: the 2-core of a connected graph is connected, so the two wordings name one object
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 6.5, p.21

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Lemma 6.5, p.21, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). With `α = ε^{1/ε²⁰}`, `m = ε²2^{αd}` and `M = ε⁻²2^{αd}`, under the standing
assumptions of §6, whp every `Q^d_p`-special `(a, b)`-tree `T ⊆ C₂` of order `s` with
`m/d⁴ ≤ s ≤ Md⁵` satisfies `b < ε¹⁰s` and `a ≤ 1000εs`; if in addition `T` is almost interior-closed
in `C₂`, then `a ≥ εs/1000`. -/
theorem lemma_6_5 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
        ∀ (T : (coreGraph (openGraph ω) L₁).Subgraph) (a b : ℕ), IsSpecial (openGraph ω) T a b →
          mLow ε d / (d : ℝ) ^ 4 ≤ (T.verts.ncard : ℝ) →
          (T.verts.ncard : ℝ) ≤ mHigh ε d * (d : ℝ) ^ 5 →
          (b : ℝ) < ε ^ 10 * T.verts.ncard ∧ (a : ℝ) ≤ 1000 * ε * T.verts.ncard ∧
          (IsAlmostInteriorClosed (coreGraph (openGraph ω) L₁) T →
            ε * T.verts.ncard / 1000 ≤ (a : ℝ)) := by sorry

end PercCubeCycles
