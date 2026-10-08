-- Prove2me | Theorems.Thm_PrivLearn_LocalSim_randomizer_is_local
-- name    : PrivLearn.LocalSim.randomizer_is_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:06.147486+00:00
-- url     : https://prove2.me/theorems/1f68c796-712e-4ba5-834a-589e550d7e28
-- title:
--   §5.1.1, p. 20 — R_g(u) = g(u) + Lap(2b/ε) is an ε-local randomizer
-- statement:
--   Let $g:D\to[-b,b]$ with $b>0$, and let $\varepsilon>0$. The randomizer $R_g(u)=g(u)+\eta$, where $\eta\sim\mathrm{Lap}(2b/\varepsilon)$, is an $\varepsilon$-local randomizer: for all inputs $u,u'\in D$ and every measurable $S\subseteq\mathbb R$,
--   $$\Pr[R_g(u)\in S]\le e^{\varepsilon}\,\Pr[R_g(u')\in S].$$
--
--   The paper derives this from the Laplace mechanism (Theorem 2.3), since $|g(u)-g(u')|\le 2b$. It is the single privacy fact that every query of the simulation rests on.
--
--   **Formalization Note.** $R_g(u)$ is the law of $g(u)+\eta$, the push-forward of $\mathrm{Lap}(2b/\varepsilon)$ under $x\mapsto g(u)+x$. No measurability of $g$ is needed, since the input $u$ is fixed.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 20, §5.1.1, the sentence before the box defining A_g

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy
import Definitions.Def_PrivLearn_LocalSim_Simulation

namespace PrivLearn.LocalSim

open MeasureTheory

/-- §5.1.1 (p. 20): for a query `g : Dom → [−b, b]`, the randomizer `R_g(u) = g(u) + η` with
`η ∼ Lap(2b/ε)` is an ε-local randomizer. -/
theorem randomizer_is_local {Dom : Type*} (g : Dom → ℝ) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hg : ∀ u, |g u| ≤ b) :
    IsLocalRandomizer (randomizerLaw g (2 * b / ε)) ε := by sorry

end PrivLearn.LocalSim
