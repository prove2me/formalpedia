-- Prove2me | Theorems.Thm_SelmerGroup_shaTors_finite
-- name    : SelmerGroup.shaTors_finite
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T15:59:35.734151+00:00
-- url     : https://prove2.me/theorems/1f858309-9345-43f7-aeb7-f2d7956f9d6b
-- title:
--   $\text{Ш}(E/K)[n]$ is finite
-- statement:
--   Let $K$ be a number field, $E/K$ an elliptic curve and $n\ge1$. The $n$-torsion of the Tate–Shafarevich group,
--   $$\text{Ш}(E/K)[n]=\{\xi\in\text{Ш}(E/K): n\xi=0\}\subseteq H^1(G_K,E(\bar K)),$$
--   is finite.
--
--   This is the finiteness of the part of $\text{Ш}$ killed by the isogeny $[n]$; the finiteness of all of $\text{Ш}(E/K)$ is a conjecture and is not claimed.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1
import Definitions.Def_SelmerGroup_GaloisPoints
import Definitions.Def_SelmerGroup_Selmer

open NumberField

namespace SelmerGroup
theorem shaTors_finite {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    [E.IsElliptic] (n : ℕ) (hn : 0 < n) :
    (shaTors E n).Finite := by sorry
end SelmerGroup
