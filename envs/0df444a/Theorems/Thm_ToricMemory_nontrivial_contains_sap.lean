-- Prove2me | Theorems.Thm_ToricMemory_nontrivial_contains_sap
-- name    : ToricMemory.nontrivial_contains_sap
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:42.215823+00:00
-- url     : https://prove2.me/theorems/980dd9a1-51e9-461b-946a-fe2559540176
-- title:
--   Nontrivial cycles contain self-avoiding polygons with at least $L$ horizontal links
-- statement:
--   On the $L\times L\times T$ spacetime torus:
--
--   1. every cycle $C$ ($\partial C=\emptyset$) with odd $x$-winding or odd $y$-winding contains the link set of a rooted self-avoiding polygon on the torus which itself has odd $x$-winding or odd $y$-winding;
--   2. every rooted self-avoiding polygon on the torus with odd $x$-winding or odd $y$-winding has at least $L$ horizontal links.
--
--   The paper uses these two facts to restrict the failure event to self-avoiding polygons with $H\ge L$ in (55).
--
--   Differences from the source:
--   - reading: E + E_min contains homologically nontrivial paths (p. 20) → E Δ E_min contains a cycle (empty boundary) with odd x-winding or odd y-winding (Fails); reason: on the 3-torus a cycle winding only in time has no horizontal link, while p. 20 says a damaging path has at least L horizontal links; the event contains the event that the class of E Δ E_min is nontrivial
--   - generalization: a homologically nontrivial closed walk (part 1) → any ℤ₂-cycle C with odd x- or y-winding; reason: the link set of a closed walk using each link at most once is such a cycle
--   - reading: a self-avoiding polygon obtained by eliminating links → a rooted torus SAP whose link set is contained in C, with odd winding; reason: the polygon obtained must itself be nontrivial for the paper's use; a polygon is a closed walk listed as oriented links
--   - reading: a spacetime lattice of L×L sites over T time slices, with L²T sites, 2L²T horizontal and L²T vertical links (Sec. V B–C, pp. 19–20) → the 3-torus ZMod L × ZMod L × ZMod T with periodic time; links are (site, direction) pairs; reason: the counts printed on p. 20 are exactly those of the 3-torus; an open-time slab has L²(T−1) vertical links
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, p. 19 ("given any homologically nontrivial closed walk, we can obtain a closed SAW (a self-avoiding polygon, or SAP) by eliminating some links") and p. 20 ("the homologically nontrivial (self-avoiding) path must contain at least L horizontal links")

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_IsMLDecoder
import Definitions.Def_ToricMemory_Failure
import Definitions.Def_ToricMemory_TorusSAP

open Finset

namespace ToricMemory

/-- **Homologically nontrivial cycles contain long self-avoiding polygons**,
arXiv:quant-ph/0110143v1, Sec. V B, p. 19 ("given any homologically nontrivial closed walk, we
can obtain a closed SAW (a self-avoiding polygon, or SAP) by eliminating some links") and p. 20
("At a minimum, the homologically nontrivial (self-avoiding) path must contain at least `L`
horizontal links").

1. Every cycle `C` (`∂C = ∅`) with odd `x`- or `y`-winding contains the link set of a rooted
   self-avoiding polygon on the torus that itself has odd `x`- or `y`-winding.
2. Every self-avoiding polygon on the torus with odd `x`- or `y`-winding has at least `L`
   horizontal links.

**Formalization Note** "Homologically nontrivial" is read as an odd winding around a spatial
direction of the torus (`Fails`); a cycle winding only in time does not damage the encoded
information. -/
theorem nontrivial_contains_sap {L T : ℕ} [NeZero L] [NeZero T] :
    (∀ C : Finset (Link L T), boundary C = ∅ → (Odd (xWind C) ∨ Odd (yWind C)) →
      ∃ (s : Site L T) (n : ℕ) (w : Fin n → Link L T × Bool), IsTorusSAP s w ∧
        linkSet w ⊆ C ∧ (Odd (xWind (linkSet w)) ∨ Odd (yWind (linkSet w)))) ∧
    (∀ (s : Site L T) (n : ℕ) (w : Fin n → Link L T × Bool), IsTorusSAP s w →
      (Odd (xWind (linkSet w)) ∨ Odd (yWind (linkSet w))) → L ≤ hCount (linkSet w)) := by sorry

end ToricMemory
