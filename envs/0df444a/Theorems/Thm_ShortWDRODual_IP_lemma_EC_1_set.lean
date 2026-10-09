-- Prove2me | Theorems.Thm_ShortWDRODual_IP_lemma_EC_1_set
-- name    : ShortWDRODual.IP.lemma_EC_1_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:47.160219+00:00
-- url     : https://prove2.me/theorems/d4760e21-3a17-4b4b-a54f-29bc183b4c23
-- title:
--   Lemma EC.1 (sets), p. ec2 — A is diagonally dominant iff its indicator 1_A is
-- statement:
--   Let $(\mathcal X,\mathcal F)$ be a measurable space and $A\subset\mathcal X\times\mathcal X$. Then
--
--   $$A \text{ is a diagonally dominant set} \iff \mathbf 1_A \text{ is a diagonally dominant function},$$
--
--   where $\mathbf 1_A(\widehat x,x)=1$ on $A$ and $0$ off $A$. Both sides include $(\mathcal F\otimes\mathcal F)$-measurability (of $A$, resp. of $\mathbf 1_A$).
--
--   This is the first of three observations translating diagonal dominance between sets, functions and set-valued maps; it is what makes the indicator of a diagonally dominant set a legitimate test function in the necessity part of Proposition 1.
--
--   **Formalization Note** The indicator takes values in `EReal`.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma EC.1, first sentence, p. ec2 (PDF p. 16)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem lemma_EC_1_set {X : Type*} [MeasurableSpace X] (A : Set (X × X)) :
    DiagDomSet A ↔ DiagDomFun (A.indicator (fun _ => (1 : EReal))) := by sorry

end ShortWDRODual.IP
