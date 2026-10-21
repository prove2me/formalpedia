-- Prove2me | Theorems.Thm_VWAPContract_Optimal_proposition_5_strict_ic
-- name    : VWAPContract.Optimal.proposition_5_strict_ic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:54.448121+00:00
-- url     : https://prove2.me/theorems/bd2b72d9-437d-4c28-86f8-752fbd247c51
-- title:
--   Proof of Proposition 5, p. 53 (PDF 54) — under $\tau^{VWAP}$, $E[u(\tau-p\cdot x)]\le u(0)$ with equality iff $x=x^{FB}$ a.s.
-- statement:
--   For every admissible static policy $x(\eta)$ under the guaranteed VWAP contract, the dealer's expected utility obeys
--
--   $$\mathbb E[u(\tau^{\mathrm{VWAP}}-p\cdot x)]\le u(0),$$
--
--   with equality if and only if $x(\eta)=x^{\mathrm{FB}}(\eta)$ almost surely. Thus any policy differing from first best on a set of positive probability yields strictly lower expected utility. This is the stronger incentive claim stated in the proof of Proposition 5.
--
--   **Formalization Note** The deviation's dealer utility is assumed integrable so its real-valued expectation represents the payoff in the paper.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 53 (PDF 54), proof of Proposition 5, the paragraph after (11)–(12) and the strict (IC) display

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem proposition_5_strict_ic {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing) :
    ∀ X : (Fin T → ℝ) → (Fin T → ℝ), IsPolicy X →
      Integrable (dealerUtil M tauVWAP X) M.P →
      dealerEU M tauVWAP X ≤ M.u 0 ∧
      (dealerEU M tauVWAP X = M.u 0 ↔
        (fun ω => X (M.eta ω)) =ᵐ[M.P] fun ω => xFB (M.eta ω)) := by sorry

end VWAPContract.Optimal
