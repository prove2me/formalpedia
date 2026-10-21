-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_remark_1
-- name    : SWSSNet.Diffusion.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:08.943756+00:00
-- url     : https://prove2.me/theorems/4508435a-fc26-4d69-bc84-9913a7790380
-- title:
--   Remark 1 — the sign of ϑ_p does not depend on the positive vector p
-- statement:
--   For any two positive probability vectors $p,p'$ on the classes, the SWSS parameters $\vartheta_p$ and $\vartheta_{p'}$ have the same sign:
--   $$
--   \operatorname{sign}\vartheta_p=\operatorname{sign}\vartheta_{p'}.
--   $$
--
--   So the conditions $\vartheta_p>0$, $\vartheta_p<0$ and $\vartheta_p=0$ in Theorem 1 are properties of the network alone. This is what allows the proof of stability to switch to a convenient vector $p$.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 8, Remark 1

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Remark 1, p. 8: the sign of `ϑ_p` does not depend on the positive probability vector `p`. -/
theorem remark_1 {I J : ℕ} (N : TreeNetwork I J) (p p' : Fin I → ℝ) (hp : IsPosProb p)
    (hp' : IsPosProb p') :
    SignType.sign (swss N p) = SignType.sign (swss N p') := by sorry

end SWSSNet.Diffusion
