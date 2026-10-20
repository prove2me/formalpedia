-- Prove2me | Theorems.Thm_VaccineAMC_Framework_lemma_1
-- name    : VaccineAMC.Framework.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:15.747463+00:00
-- url     : https://prove2.me/theorems/f0cb5155-6fe6-4993-a0cc-192a1ae89397
-- title:
--   Lemma 1 — inverse demand is positive and decreasing
-- statement:
--   Let $\theta$ satisfy the model's standing assumptions. For every price $p\in(0,\bar p)$, the extended demand curve agrees with the inverse of $P$ and has a strictly negative derivative:
--
--   $$D(p)>0,\qquad P(D(p))=p,\qquad D'(p)<0.$$
--
--   This identifies the economically relevant branch of demand used by all three capacity results. **Formalization Note** Demand is real valued, so finiteness is automatic; the derivative is expressed by the existence of a negative derivative value.
-- source:
--   Kremer, Levin & Snyder, Designing Advance Market Commitments for New Vaccines, BFI Working Paper No. 2020-175 (Dec. 2020), p. 6 (PDF 9), Lemma 1

import Mathlib
import Definitions.Def_VaccineAMC_Framework_Model

open Filter Topology

namespace VaccineAMC.Framework

theorem lemma_1 (θ : Params) (hS : θ.Standing) (p : ℝ)
    (hp : p ∈ Set.Ioo 0 (pbar θ)) :
    0 < demand θ p ∧ invDemand θ (demand θ p) = p ∧
      ∃ d : ℝ, d < 0 ∧ HasDerivAt (demand θ) d p := by sorry

end VaccineAMC.Framework
