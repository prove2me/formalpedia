-- Prove2me | Theorems.Thm_UnderstandingML_ldim_le_mistake_bound
-- name    : UnderstandingML.ldim_le_mistake_bound
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:11:17.227967+00:00
-- url     : https://prove2.me/theorems/d282a96f-4bae-4ab4-8883-8f88deeaeb7e
-- title:
--   Lemma 21.6: no algorithm has a mistake bound smaller than Ldim(H): M_A(H) ≥ Ldim(H) for every A
-- statement:
--   **Lemma 21.6.** No algorithm can have a mistake bound strictly smaller than $\operatorname{Ldim}(H)$; namely, for every algorithm $A$, we have $M_A(H) \ge \operatorname{Ldim}(H)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.1.1 p. 291, Lemma 21.6

import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Lemma 21.6** (p. 291). No algorithm can have a mistake bound strictly smaller than
`Ldim(H)`; namely, for every algorithm `A`, we have `M_A(H) ≥ Ldim(H)`. -/
theorem ldim_le_mistake_bound {X : Type*} (H : Set (X → Bool)) (A : OnlineAlg X Bool) :
    ldim H ≤ mistakeBound A H := by sorry

end UnderstandingML
