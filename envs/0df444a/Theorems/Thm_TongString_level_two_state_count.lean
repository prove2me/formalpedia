-- Prove2me | Theorems.Thm_TongString_level_two_state_count
-- name    : TongString.level_two_state_count
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:53:40.33914+00:00
-- url     : https://prove2.me/theorems/6cfb12ec-f98e-4a6c-96e3-25d6d740bf62
-- title:
--   Level-2 counting: $\frac12(D-2)(D-1)+(D-2)=\frac12D(D-1)-1$
-- statement:
--   Let $D\ge2$. In one (say right-moving) sector, the states of the lightcone string at level $N=2$ are $\alpha^i_{-1}\alpha^j_{-1}|0\rangle$, one for each unordered pair $\{i,j\}$ of transverse indices $i,j\in\{1,\dots,D-2\}$ (repetition allowed), and $\alpha^i_{-2}|0\rangle$, one for each $i$. Their number is
--
--   $$
--   \tfrac12(D-2)(D-1)+(D-2)=\tfrac12D(D-1)-1,
--   $$
--
--   which is the dimension of the traceless symmetric tensor representation of $SO(D-1)$. This is Tong's observation that the massive level-2 states fit into a representation of the little group $SO(D-1)$.
--
--   **Formalization Note** The unordered pairs with repetition are counted as the cardinality of `Sym2 (Fin (D-2))`; natural-number subtraction and division are exact here since $D\ge2$ and $D(D-1)$ is even.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 2.3.3, p. 45 ('In the left-moving sector, we have ½(D − 2)(D − 1) + (D − 2) = ½D(D − 1) − 1')

import Mathlib

namespace TongString

theorem level_two_state_count (D : ℕ) (hD : 2 ≤ D) :
    Fintype.card (Sym2 (Fin (D - 2))) + (D - 2) = D * (D - 1) / 2 - 1 := by sorry

end TongString
