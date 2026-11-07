-- Prove2me | Theorems.Thm_PredAdvice_lemma_3_7
-- name    : PredAdvice.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:54.249202+00:00
-- url     : https://prove2.me/theorems/2cdc3e60-3363-4c07-a581-75b18ca76629
-- title:
--   Lemma 3.7 — subpaths of separated small pairs are separated small pairs
-- statement:
--   Let $2\le D\le|V|$, $L\ge1$ and let $\chi$ be any colourings. Let $v$ be reachable from $u$ and let $x,y$ satisfy
--   $$
--   \mathrm{dist}(u,x)+\mathrm{dist}(x,y)+\mathrm{dist}(y,v)=\mathrm{dist}(u,v),
--   $$
--   that is, $x$ precedes or equals $y$ on some shortest $u$–$v$ path. Then $H_{x,y}\subseteq H_{u,v}$, and if $(u,v)$ is a separated small pair and $x\ne y$, then $(x,y)$ is a separated small pair.
--
--   The lemma lets the tree constructions of §4 pass from a pair to its subpairs.
--
--   Differences from the source:
--   - encoding: x, y on a shortest u–v path P, x preceding or equal to y → v reachable from u and dist(u, x) + dist(x, y) + dist(y, v) = dist(u, v); reason: equivalent: such x, y lie in this order on a concatenation of shortest paths, and conversely
--   - generalization: separation with respect to the colourings χ fixed in Lemma 3.3 → separation with respect to any colourings χ : Fin L → V → Fin (2D); reason: the proof uses no property of the specific colourings; the paper's χ is one instance
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), Lemma 3.7, p.15

import Mathlib
import Definitions.Def_PredAdvice_IsSeparated

set_option autoImplicit false

namespace PredAdvice

/-- **Lemma 3.7** (Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.5, p.15). Let `P` be a shortest `u–v` path and let `x, y ∈ P` with `x`
preceding or equal to `y` on `P`. Then `H_{x,y} ⊆ H_{u,v}`. In addition, if `(u, v)` is a separated
small pair and `x ≠ y`, then `(x, y)` is a separated small pair.

**Formalization Note** "`x, y` lie in this order on some shortest `u–v` path" is written as: `v` is
reachable from `u` and `dist(u, x) + dist(x, y) + dist(y, v) = dist(u, v)`, which is equivalent.
The colourings `χ` are arbitrary and `2 ≤ D ≤ n`, `L ≥ 1` are the section's standing assumptions. -/
theorem lemma_3_7 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (D L : ℕ)
      (χ : Colorings V D L), 2 ≤ D → D ≤ Fintype.card V → 1 ≤ L →
      ∀ u v x y : V, Reachable G u v →
        dist G u x + dist G x y + dist G y v = dist G u v →
        H G x y ⊆ H G u v ∧ (IsSeparated G χ u v → x ≠ y → IsSeparated G χ x y) := by sorry

end PredAdvice
