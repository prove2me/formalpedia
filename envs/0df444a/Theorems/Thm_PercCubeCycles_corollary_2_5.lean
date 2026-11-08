-- Prove2me | Theorems.Thm_PercCubeCycles_corollary_2_5
-- name    : PercCubeCycles.corollary_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:31.538053+00:00
-- url     : https://prove2.me/theorems/51ca5a82-e010-4bf2-badc-f439e057856f
-- title:
--   Corollary 2.5 — components outside $C_2$ have at most $d^3$ vertices; bare paths of $C_2$ at most $d^3-3$
-- statement:
--   Let $\varepsilon>0$ be sufficiently small, $p=(1+\varepsilon)/d$, and let $C_2$ be the 2-core of the giant component $L_1$ of $Q^d_p$. Whp every component of $Q^d_p-V(C_2)$ has at most $d^3$ vertices and every bare path of $C_2$ has at most $d^3-3$ vertices.
--
--   This shows that the 2-core captures the large-scale structure of the giant.
--
--   Differences from the source:
--   - encoding: $\varepsilon$ sufficiently small → $\exists\varepsilon_0>0\ \forall\varepsilon\in(0,\varepsilon_0)$; reason: the standard meaning of the phrase
--   - reading: the giant component $L_1$ → every vertex set of a largest component; reason: the page assumes a unique giant; the statement for every largest component covers ties and is not the weaker reading
--   - encoding: $Q^d_p-V(C_2)$ → `restrict` to the complement of $V(C_2)$; a vertex of $C_2$ is an isolated singleton there; reason: a singleton meets the bound for $d\ge1$, and whp sees only large $d$
--   - encoding: at most $d^3-3$ vertices → number of vertices plus $3$ is at most $d^3$; reason: avoids natural-number subtraction
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Corollary 2.5, p.7

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation
import Definitions.Def_PercCubeCycles_Trees
import Definitions.Def_PercCubeCycles_Percolation

set_option autoImplicit false

open RandomGames.BRD

namespace PercCubeCycles

/-- Corollary 2.5, p.7, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For small `ε > 0` and `p = (1 + ε)/d`, with `C₂` the 2-core of the giant
component `L₁` of `Q^d_p`, whp every component of `Q^d_p − V(C₂)` has at most `d³` vertices and every
bare path of `C₂` has at most `d³ − 3` vertices.

**Formalization Note.** `Q^d_p − V(C₂)` is `restrict` to the complement of `V(C₂)`, in which a vertex
of `C₂` is an isolated singleton; a singleton meets the bound for `d ≥ 1`. The number of vertices of
a path is its `support` length; `+ 3` avoids natural subtraction. -/
theorem corollary_2_5 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Whp (supercritical ε) fun d ω => ∀ L₁, IsLargestComponent (openGraph ω) L₁ →
        (∀ S, IsComponentSet (restrict (openGraph ω) (twoCore (restrict (openGraph ω) L₁))ᶜ) S →
          S.card ≤ d ^ 3) ∧
        ∀ (u v : Profile d) (P : (coreGraph (openGraph ω) L₁).Walk u v), IsBarePath _ P →
          P.support.length + 3 ≤ d ^ 3 := by sorry

end PercCubeCycles
