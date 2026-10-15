-- Prove2me | Theorems.Thm_OutpatientWalkIn_Triage_walkin_intensity_SWB
-- name    : OutpatientWalkIn.Triage.walkin_intensity_SWB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:16.75501+00:00
-- url     : https://prove2.me/theorems/2c40b133-3b16-4a9f-9105-49b8962e7524
-- title:
--   Proof of Proposition 6 (2)(b), Online App. p. 37 — in Regime SWB, (λ^{s,t*}_W + λ_E)/µ_W = λ_E/µ̲_W
-- statement:
--   Assume the standing assumptions and let $\underline\mu_W>0$ satisfy (15), $R-C_W\,w(\lambda_E/\underline\mu_W)=0$. Let $\mu_S\in[0,\mu)$, $\mu_W=\mu-\mu_S$, and let $(\delta,p_W,p_B)$ be an observable equilibrium at $\mu_S$ in which some strategic patients walk in and some balk, $p_W>0$ and $p_B>0$ (Regime SWB). Then
--   $$\frac{\lambda p_W+\lambda_E}{\mu_W}=\frac{\lambda_E}{\underline\mu_W}.$$
--
--   When patients mix between walking in and balking, they are indifferent, so walking in is worth exactly zero and the walk-in intensity is pinned at the level defined by (15). The proof of part 2 of Proposition 6 uses this identity.
--
--   **Formalization Note** The paper conditions on "$\mu<\overline\mu_O$, i.e., the equilibrium … is in SWB regime"; the statement is conditioned on the regime itself ($p_W>0$, $p_B>0$). The strategic walk-in rate $\lambda^{s,t*}_W$ is $\lambda p_W$.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 37, proof of Proposition 6 (2), case (b)

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting

namespace OutpatientWalkIn.Triage

theorem walkin_intensity_SWB (M : Model) (hM : M.Standing) (μWl : ℝ) (hμWl : 0 < μWl)
    (h15 : M.R - M.CW * M.w (M.lamE / μWl) = 0) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e → 0 < e.pW → 0 < e.pB →
      (M.lam * e.pW + M.lamE) / (M.mu - μS) = M.lamE / μWl := by sorry

end OutpatientWalkIn.Triage
