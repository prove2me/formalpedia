-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_lemma_27
-- name    : TFIMPhaseDiagram.Classical.Supplement.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:05:43.154543+00:00
-- url     : https://prove2.me/theorems/2c9400f2-b00d-4ee5-8ba8-37f8b13aa4fc
-- title:
--   Lemma 27 — Quadratic functional gap for every L² field
-- statement:
--   Fix $b,\eta>0$ with $(b/\eta)\tanh\eta>1$, and let $m_\ast$ be the positive magnetization from Proposition 26. There is a positive constant depending only on $b,\eta$ such that every $q\in L^2(S)$ satisfies
--   $$
--   \Phi_{b,\eta}(bm_\ast1)-\Phi_{b,\eta}(bq)\ge c\min_{s\in\{-1,1\}}\|q-sm_\ast1\|^2.
--   $$
--   The statement chooses the witness computed on p.18,
--   $$c=\min\!\left\{\frac{c_1}{13},\frac{b\,\operatorname{sech}\eta\,e^{-3bm_\ast/2}(1-e^{-bm_\ast/2})}{4m_\ast}\right\}>0.$$
--   There is no sign restriction on $q$. The estimate is the uniform gap underlying the rate-function bound.
--
--   Differences from the source:
--   - encoding: a positive parameter-dependent constant c, evaluated explicitly in the proof on p.18 → the shared functionalGap definition with that exact proof witness; reason: makes the source witness uniform and common to the subsequent rate and concentration statements
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 16, Lemma 27

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Lemma 27, p.16. The positive witness is the one computed on p.18. -/
theorem lemma_27 (b η : ℝ) (h : supercritical b η) :
    IsMagnetization b η (magnetization b η) ∧ 0 < functionalGap b η ∧
    ∀ q : CircleL2, functionalGap b η * phaseDistanceSq (magnetization b η) q ≤
      phi b η (constL2 (b * magnetization b η)) - phi b η (b • q) := by sorry

end TFIMPhaseDiagram.Classical.Supplement
