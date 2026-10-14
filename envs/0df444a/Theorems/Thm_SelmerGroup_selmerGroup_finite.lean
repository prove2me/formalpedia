-- Prove2me | Theorems.Thm_SelmerGroup_selmerGroup_finite
-- name    : SelmerGroup.selmerGroup_finite
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:01:43.418985+00:00
-- url     : https://prove2.me/theorems/3a13945d-0266-4b78-908d-6783055b07fe
-- title:
--   The $n$-Selmer group of an elliptic curve over a number field is finite
-- statement:
--   Let $K$ be a number field, $E/K$ an elliptic curve and $n\ge1$. Then the $n$-Selmer group
--   $$\mathrm{Sel}^{(n)}(E/K)=\bigcap_{v}\ker\Big(H^1(G_K,E(\bar K)[n])\to H^1(G_{K_v},E(\bar K_v)[n])/\mathrm{im}\,\kappa_v\Big),$$
--   where $v$ runs over all finite and infinite places of $K$ and $\kappa_v$ is the local Kummer map, is finite.
--
--   This is the finiteness statement for the Selmer group of the isogeny $[n]:E\to E$; it implies the weak Mordell–Weil theorem and the finiteness of $\text{Ш}(E/K)[n]$.
--
--   **Formalization Note** The Selmer group is a subset of the continuous cohomology group $H^1(G_K,E(\bar K)[n])$; the theorem asserts this subset is finite.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1
import Definitions.Def_SelmerGroup_GaloisPoints
import Definitions.Def_SelmerGroup_Selmer

open NumberField

namespace SelmerGroup
theorem selmerGroup_finite {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    [E.IsElliptic] (n : ℕ) (hn : 0 < n) :
    (selmerGroup E n).Finite := by sorry
end SelmerGroup
