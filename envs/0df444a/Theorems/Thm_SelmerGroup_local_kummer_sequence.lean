-- Prove2me | Theorems.Thm_SelmerGroup_local_kummer_sequence
-- name    : SelmerGroup.local_kummer_sequence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T15:57:27.738262+00:00
-- url     : https://prove2.me/theorems/76e88078-c316-47b8-8cab-ec90b10ceeb7
-- title:
--   Local Kummer sequence: $H^1(G_{K_v},E[n])/\mathrm{im}\,\kappa_v\cong H^1(G_{K_v},E)[n]$
-- statement:
--   Let $K$ be a number field, $E/K$ an elliptic curve, $n\ge1$, and $L$ any field containing $K$ (for instance a completion $K_v$). Let $j_L:H^1(G_L,E(\bar L)[n])\to H^1(G_L,E(\bar L))$ be induced by inclusion and $\mathrm{im}\,\kappa_L$ the image of the Kummer map. Then
--
--   1. for every $\xi\in H^1(G_L,E[n])$: $\ j_L(\xi)=0 \iff \xi\in\mathrm{im}\,\kappa_L$;
--   2. the image of $j_L$ is exactly the $n$-torsion:
--   $$j_L\big(H^1(G_L,E[n])\big)=H^1(G_L,E)[n].$$
--
--   Together these say $H^1(G_L,E[n])/\mathrm{im}\,\kappa_L\cong H^1(G_L,E)[n]$, which the source notes for $L=K_v$.
--
--   **Formalization Note** The statement is made for an arbitrary field $L$ over $K$ (hence of characteristic $0$), which covers every completion $K_v$.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1
import Definitions.Def_SelmerGroup_GaloisPoints
import Definitions.Def_SelmerGroup_Selmer

open NumberField

namespace SelmerGroup
theorem local_kummer_sequence {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    [E.IsElliptic] (n : ℕ) (hn : 0 < n) (L : Type*) [Field L] [Algebra K L] :
    (∀ ξ : H1 (absTorsAct E L n), torsInclH1 E L n ξ = 0 ↔ ξ ∈ kummerImage E L n) ∧
    Set.range (torsInclH1 E L n) = {η : H1 (absAct E L) | n • η = 0} := by sorry
end SelmerGroup
