-- Prove2me | Theorems.Thm_ShortWDRODual_IP_lemma_EC_1_fun
-- name    : ShortWDRODual.IP.lemma_EC_1_fun
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:44.360762+00:00
-- url     : https://prove2.me/theorems/0fe0116f-7b4d-497c-9db1-934c2ec39de8
-- title:
--   Lemma EC.1 (functions), p. ec2 — φ is diagonally dominant iff every superlevel set {φ > α} is
-- statement:
--   Let $(\mathcal X,\mathcal F)$ be a measurable space and $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$. Then
--
--   $$\phi \text{ is a diagonally dominant function} \iff \{\phi>\alpha\}=\{(\widehat x,x):\phi(\widehat x,x)>\alpha\}\text{ is a diagonally dominant set for every }\alpha\in\mathbb R.$$
--
--   Both sides include $(\mathcal F\otimes\mathcal F)$-measurability (of $\phi$, resp. of every superlevel set).
--
--   This observation is what lets the measurable projection condition (Proj), stated for sets, control the measurability of $\Phi(\widehat x)=\sup_x\phi(\widehat x,x)$ through its superlevel sets.
--
--   **Formalization Note** $\phi$ is `EReal`-valued and never $+\infty$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma EC.1, second sentence, p. ec2 (PDF p. 16)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

namespace ShortWDRODual.IP

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

theorem lemma_EC_1_fun {X : Type*} [MeasurableSpace X] (φ : X × X → EReal)
    (hφtop : ∀ p, φ p ≠ ⊤) :
    DiagDomFun φ ↔ ∀ α : ℝ, DiagDomSet {p | (α : EReal) < φ p} := by sorry

end ShortWDRODual.IP
