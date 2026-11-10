-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_lemma_5_5
-- name    : Random2SATWindow.CriticalLaw.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:18.917239+00:00
-- url     : https://prove2.me/theorems/394e7ad4-64e6-4f36-b9fa-aba9cd04e974
-- title:
--   Lemma 5.5 — zero-free coefficient disk: $B_0(\cdot,w)\ne0$ on $|z|\le\varrho(w)$
-- statement:
--   There exists $w_0>0$ such that, for every $w\in(0,w_0)$, $B_0(z,w)=\big(e^{-S_0(z,w)}\odot D_0(z,w)\big)$ has no zero in the closed disk $|z|\le\varrho(w)=\dfrac1{ew(1+w)}$.
--
--   Differences from the source:
--   - encoding: B_0(z, w), the entire function e^{-S_0(z,w)} ⊙ D_0(z,w) with S_0 from (47) → B0 z w = Σ' k, [z^k](expHadamard (expOf (−S0 w)) (D0 w)) · z^k; reason: B_0 is entire in z for w > 0 (coefficients carry (1+w)^{-C(k,2)}), so the tsum is its value
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Lemma 5.5, printed p. 45 (PDF 47)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **Lemma 5.5** (zero-free coefficient disk, printed p. 45 / PDF 47). There exists `w_0 > 0`
such that, for every `w ∈ (0, w_0)`, `B_0(z, w)` has no zero in the closed disk
`|z| ≤ ϱ(w) = 1/(e w (1 + w))`. -/
theorem lemma_5_5 :
    ∃ w0 : ℝ, 0 < w0 ∧ ∀ w : ℝ, 0 < w → w < w0 →
      ∀ z : ℂ, ‖z‖ ≤ coeffRadius w → B0 z w ≠ 0 := by sorry

end Random2SATWindow.CriticalLaw
