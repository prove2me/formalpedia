-- Prove2me | Theorems.Thm_RiskExposure_Complementarity_auxiliary_lemma
-- name    : RiskExposure.Complementarity.auxiliary_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:55.686723+00:00
-- url     : https://prove2.me/theorems/97f8a978-05e6-41fa-9dcd-2d4c2324227f
-- title:
--   Auxiliary Lemma, Internet Appendix p. 7 — d*(ω) is higher when a bank's project succeeds than when it fails
-- statement:
--   In the setting of the mission (interbank liabilities $\bar d_{ij}\ge0$ with $\bar d_j>0$, deposits $v_i>0$, no-default assumption $\underline Z\ge v_i+\bar d_i$), fix a risk vector $Z\in[\underline Z,\overline Z]^N$. For every state $\omega$ and every bank $j$, let $\omega^{j=s}$ and $\omega^{j=f}$ be $\omega$ with bank $j$'s project set to success and to failure. Then, componentwise,
--   $$d^*(\omega^{j=f};Z)\ \le\ d^*(\omega^{j=s};Z).$$
--
--   This is the "in particular" part of the Auxiliary Lemma: every bank's payment weakly increases when any single project succeeds. It drives the sign of every comparative-statics step of Proposition 1.
--
--   **Formalization Note** Only the state form of the lemma is stated; its first sentence (monotonicity in a general cash-flow vector) would need a clearing map indexed by arbitrary cash flows and is not posed. $d^*$ is the greatest payment equilibrium.
-- source:
--   Shu, Endogenous Risk Exposure and Systemic Instability, Management Science, doi:10.1287/mnsc.2022.01519 (accepted manuscript, 17 Sep 2024), Internet Appendix p. 7, Auxiliary Lemma

import Mathlib
import Definitions.Def_RiskExposure_Complementarity_Model

namespace RiskExposure.Complementarity

theorem auxiliary_lemma {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dbar : ι → ι → ℝ) (hdbar : ∀ i j, 0 ≤ dbar i j) (hdbarTot : ∀ j, 0 < dbarTot dbar j)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (Zlo Zhi : ℝ) (hZ : Zlo ≤ Zhi) (hnd : ∀ i, v i + dbarTot dbar i ≤ Zlo)
    (Z : ι → ℝ) (hZbox : ∀ j, Z j ∈ Set.Icc Zlo Zhi) :
    ∀ (ω : ι → Bool) (j : ι),
      paymentEq dbar v (Function.update ω j false) Z ≤
        paymentEq dbar v (Function.update ω j true) Z := by sorry

end RiskExposure.Complementarity
