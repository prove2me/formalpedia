-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_theorem_1
-- name    : SocialManip.Beliefs.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:15:06.127083+00:00
-- url     : https://prove2.me/theorems/f882f605-b7e6-4eba-a1ea-b87daa52bad9
-- title:
--   Theorem 1, p. 9 (corrected: fixed-state comparison) — generic essential uniqueness
-- statement:
--   Fix the finite network, sophistication types, qualities, prior $q\in(0,1)$ and principal capacity $\lambda^*>0$. There is a Lebesgue-null set $P\subset\mathbb R_{>0}^2\times(-1,1)$ such that for every $(\varepsilon,\lambda,b)\notin P$ in that domain satisfying Assumption 1, the following holds. For every $\kappa>0$, all sufficiently large physical horizons $T$ and every pair of equilibria, possibly equal, give
--   $$\mathbb P\{k^{(1)}=k^{(2)}\mid y\}\ge1-\kappa\qquad(y=S,R).$$
--   Here the two equilibrium realizations are independent conditional on the same fixed realized state. Each manipulated count compares strategic and truthful worlds with the same organic news. The null set precedes all varied parameters.
--
--   This states generic essential uniqueness separately in each state, as required by the fixed-state payoff comparison in the source proof on p. 46.
--
--   **Formalization Note** The state conditioning is an explicit correction to an ambiguous displayed probability in Definition 3. If the two runs independently redraw the state from its prior, positive manipulation in S and no manipulation in R prevent a deterministic count. The theorem does not assert that incompatible unconditional interpretation.
--
--   Differences from the source:
--   - correction: Definition 3 does not explicitly condition its probability on y → independent equilibrium realizations conditional on the same realized state, for each state; reason: the p. 46 proof compares k(x) and principal payoffs at a fixed state; independent prior redraws would falsify the asserted determinism whenever only S is manipulated
--   - reading: Theorem 1 is printed before Assumption 1 → Assumption 1 at the varied parameters; reason: the governing source context and p. 46 belief-limit argument use it
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 1, p. 9; Definitions 1–3 pp. 8–9; proof p. 46

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

theorem theorem_1 {n : ℕ} (M : Model n) (hS : M.Standing) (hq : 0 < M.q ∧ M.q < 1)
    (hlamStar : 0 < M.lamStar) (adj : Fin n → Fin n → Prop) :
    ∃ Pset : Set (ℝ × ℝ × ℝ), Pset ⊆ Set.Ioi 0 ×ˢ Set.Ioi 0 ×ˢ Set.Ioo (-1) 1 ∧
      volume Pset = 0 ∧
      ∀ e l c : ℝ, 0 < e → 0 < l → -1 < c → c < 1 → (e, l, c) ∉ Pset →
        ({ M with ε := e, lam := l, b := c } : Model n).Assumption1 adj →
        EssentiallyUnique ({ M with ε := e, lam := l, b := c } : Model n) := by sorry

end SocialManip.Beliefs.Supplement
