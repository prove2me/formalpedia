-- Prove2me | Theorems.Thm_ShortWDRODual_IP_lemma_EC_1_setfun
-- name    : ShortWDRODual.IP.lemma_EC_1_setfun
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:30.120013+00:00
-- url     : https://prove2.me/theorems/ea0c7571-9b52-4325-bb47-c1fcecc30577
-- title:
--   Lemma EC.1 (set-valued maps), p. ec2 — E : 𝒳 → ℱ ∖ {∅} is diagonally dominant iff Graph(E) is
-- statement:
--   Let $(\mathcal X,\mathcal F)$ be a measurable space and let $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$, i.e. every $E(\widehat x)$ is a nonempty measurable set. Then
--
--   $$E \text{ is a diagonally dominant set-valued function} \iff \mathrm{Graph}(E)=\{(\widehat x,x):x\in E(\widehat x)\}\text{ is a diagonally dominant set}.$$
--
--   Both sides include $(\mathcal F\otimes\mathcal F)$-measurability of $\mathrm{Graph}(E)$.
--
--   This identifies the hypothesis of the weak measurable selection condition (Sel\*) with a condition on a single set.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma EC.1, third sentence, p. ec2 (PDF p. 16)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem lemma_EC_1_setfun {X : Type*} [MeasurableSpace X] (E : X → Set X)
    (hE : ∀ xh, MeasurableSet (E xh) ∧ (E xh).Nonempty) :
    DiagDomSetFun E ↔ DiagDomSet (graph E) := by sorry

end ShortWDRODual.IP
