-- Prove2me | Theorems.Thm_SustainableFashion_Variety_lemma_1
-- name    : SustainableFashion.Variety.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:30.688654+00:00
-- url     : https://prove2.me/theorems/943d3c67-a8fd-4fc6-815e-50ca5bc64e03
-- title:
--   Lemma 1, p. 10 — equally spaced styles minimise the expected distance to the trend
-- statement:
--   Place $m\ge1$ styles at points $t_1,\dots,t_m$ of a circle of unit circumference, and let the fashion trend $x$ be uniformly distributed on the circle. Write $|t^*-x|$ for the arc distance from $x$ to the nearest style. Then the equally spaced configuration $t_i=i/m$ minimises the expected nearest distance:
--   $$\mathbb E\,|t^*-x|\,\big|_{t_i=i/m}\ \le\ \mathbb E\,|t^*-x|\,\big|_{t_1,\dots,t_m}\qquad\text{for all } t_1,\dots,t_m .$$
--
--   Since the firm's expected profit depends on the style locations only through the term $-\gamma\,\mathbb E[n]\,\mathbb E|t^*-x|$, this is the paper's Lemma 1: for any number of products, it is optimal to locate them at equal distances to each other.
--
--   **Formalization Note** The Lean statement is the reduced form to which the paper's proof reduces the lemma ("It suffices to prove that $E|t^*-x|$ is minimized when the products are located at equal distances to each other", p. 38). Locations are an arbitrary map `Fin m → AddCircle 1` (coincident styles allowed).
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), Lemma 1, p. 10 (proof p. 38)

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem lemma_1 (m : ℕ) [NeZero m] (t : Fin m → Circle) :
    expNearestDist (equalSpacing m) ≤ expNearestDist t := by sorry

end SustainableFashion.Variety
