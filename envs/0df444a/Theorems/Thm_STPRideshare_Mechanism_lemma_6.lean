-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_6
-- name    : STPRideshare.Mechanism.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:37.082367+00:00
-- url     : https://prove2.me/theorems/377c1025-3cea-4e4b-a2b5-254cdee716f1
-- title:
--   Lemma 6, p. 40 — in a CE, a trip that some driver takes without a rider has a non-positive price
-- statement:
--   Let $(x,\tilde z,p)$ be a plan with anonymous trip prices that forms a competitive equilibrium in a valid economy. If some driver $i$ takes the trip $(a,b,t)$ as a relocation, i.e. without a rider, on her action path $\tilde z_i$, then
--   $$p_{a,b,t}\le 0 .$$
--
--   Trips with excess driver supply thus carry no positive price; the lemma is used to check complementary slackness in the proof of Lemma 3.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 40, Lemma 6 (Appendix B.3)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 6, p. 40: in a CE `(x, z̃, p)`, every trip that some driver takes as a relocation
(without a rider) has a non-positive price. -/
theorem lemma_6 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) (d : Dispatch e) (p : Price L) (hce : d.IsCE p) :
    ∀ (i : ι) (tr : Trip L), (tr, none) ∈ d.z i → p tr ≤ 0 := by sorry

end STPRideshare.Mechanism
