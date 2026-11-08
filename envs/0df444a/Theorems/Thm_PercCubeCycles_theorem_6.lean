-- Prove2me | Theorems.Thm_PercCubeCycles_theorem_6
-- name    : PercCubeCycles.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:39.925198+00:00
-- url     : https://prove2.me/theorems/e1d763c1-2fab-4c16-9329-967a52957455
-- title:
--   Theorem 6 — medium connected sets of $C_2$ have $\Theta(\varepsilon|S|)$ neighbours and few edges to any part of them
-- statement:
--   Let $\varepsilon>0$ be sufficiently small and $p=(1+\varepsilon)/d$. Let $\alpha=\varepsilon^{1/\varepsilon^{20}}$, $m=\varepsilon^22^{\alpha d}$ and $M=\varepsilon^{-2}2^{\alpha d}$, and let $C_2$ be the 2-core of the giant component of $Q^d_p$. Whp every connected set $S\subseteq V(C_2)$ in $C_2$ with $m\le|S|\le M+1$ satisfies:
--
--   1. $\varepsilon|S|/4000\le|N_{C_2}(S)|\le2000\varepsilon|S|$, and
--   2. for every $Z\subseteq N_{C_2}(S)$, $e_{C_2}(S,Z)\le|Z|+\varepsilon^82^{\alpha d}$.
--
--   This is exactly what Theorem 3 needs in order to find cycles in the 2-core.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small → $\exists\varepsilon_0>0\ \forall\varepsilon\in(0,\varepsilon_0)$; reason: the standard meaning of the phrase
--   - reading: the giant component $L_1$ → every vertex set of a largest component; reason: the page assumes a unique giant; the statement for every largest component covers ties and is not the weaker reading
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Theorem 6, p.10

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Theorem 6, p.10, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). With `α = ε^{1/ε²⁰}`, `m = ε²2^{αd}` and `M = ε⁻²2^{αd}`, and `C₂` the 2-core of the
giant component of `Q^d_p`, whp every connected set `S ⊆ V(C₂)` in `C₂` with `m ≤ |S| ≤ M + 1` satisfies
1. `ε|S|/4000 ≤ |N_{C₂}(S)| ≤ 2000ε|S|`, and
2. for every `Z ⊆ N_{C₂}(S)`, `e_{C₂}(S, Z) ≤ |Z| + ε⁸ 2^{αd}`.

**Formalization Note.** A connected set of `coreGraph` is automatically inside `V(C₂)` once it has
at least two vertices; `S ⊆ V(C₂)` is stated for every size. -/
theorem theorem_6 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
        ∀ S : Finset (Profile d), S ⊆ twoCore (restrict (openGraph ω) L₁) →
          IsConnectedSet (coreGraph (openGraph ω) L₁) S →
          mLow ε d ≤ (S.card : ℝ) → (S.card : ℝ) ≤ mHigh ε d + 1 →
          (ε * S.card / 4000 ≤ ((nbhd (coreGraph (openGraph ω) L₁) S).card : ℝ) ∧
            ((nbhd (coreGraph (openGraph ω) L₁) S).card : ℝ) ≤ 2000 * ε * S.card) ∧
          ∀ Z ⊆ nbhd (coreGraph (openGraph ω) L₁) S,
            (eBetween (coreGraph (openGraph ω) L₁) S Z : ℝ) ≤ Z.card + ε ^ 8 * medScale ε d := by sorry

end PercCubeCycles
