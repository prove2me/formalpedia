-- Prove2me | Theorems.Thm_UnderstandingML_soa_mistake_bound
-- name    : UnderstandingML.soa_mistake_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:11:40.544461+00:00
-- url     : https://prove2.me/theorems/e15ed1cc-243b-47d1-bcbc-7c13c0698c58
-- title:
--   Lemma 21.7 / Corollary 21.8: the Standard Optimal Algorithm has mistake bound M_SOA(H) ≤ Ldim(H)
-- statement:
--   **Lemma 21.7.** SOA enjoys the mistake bound $M_{\mathrm{SOA}}(H) \le \operatorname{Ldim}(H)$.
--
--   With Lemma 21.6 this gives **Corollary 21.8**: $M_{\mathrm{SOA}}(H) = \operatorname{Ldim}(H)$ and no other algorithm can have $M_A(H) < \operatorname{Ldim}(H)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.1.1 pp. 292-293, Lemma 21.7 and Corollary 21.8

import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 21.7** (p. 293). SOA enjoys the mistake bound `M_SOA(H) ≤ Ldim(H)`. With
Lemma 21.6 this is Corollary 21.8: `M_SOA(H) = Ldim(H)` and no algorithm does better. -/
theorem soa_mistake_bound {X : Type*} (H : Set (X → Bool)) :
    mistakeBound (soa H) H ≤ ldim H := by sorry

end UnderstandingML
