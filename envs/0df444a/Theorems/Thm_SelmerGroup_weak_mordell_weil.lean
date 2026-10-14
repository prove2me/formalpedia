-- Prove2me | Theorems.Thm_SelmerGroup_weak_mordell_weil
-- name    : SelmerGroup.weak_mordell_weil
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:00:25.910113+00:00
-- url     : https://prove2.me/theorems/e346f4e3-b36a-4ec7-aba0-4ec1e0765a3e
-- title:
--   Weak Mordell–Weil: $E(K)/nE(K)$ is finite
-- statement:
--   Let $K$ be a number field, $E/K$ an elliptic curve and $n\ge1$. The subgroup $nE(K)=\{nP:P\in E(K)\}$ has finite index in $E(K)$; equivalently,
--   $$E(K)/nE(K)\ \text{is finite}.$$
--
--   This is the weak Mordell–Weil theorem, which the source derives from the finiteness of the Selmer group.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1
import Definitions.Def_SelmerGroup_GaloisPoints
import Definitions.Def_SelmerGroup_Selmer

open NumberField

namespace SelmerGroup
theorem weak_mordell_weil {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    [E.IsElliptic] (n : ℕ) (hn : 0 < n) :
    (nsmulAddMonoidHom n : Pts E K →+ Pts E K).range.FiniteIndex := by sorry
end SelmerGroup
