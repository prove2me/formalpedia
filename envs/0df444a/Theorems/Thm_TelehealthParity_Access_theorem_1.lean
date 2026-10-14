-- Prove2me | Theorems.Thm_TelehealthParity_Access_theorem_1
-- name    : TelehealthParity.Access.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:49.850358+00:00
-- url     : https://prove2.me/theorems/1de6caea-a2ee-4cdd-aba7-9a87d8bef03e
-- title:
--   Theorem 1 — BOT is an equilibrium iff $\theta\in(\theta^T,\theta^O)$
-- statement:
--   Under the standing assumptions, let $q$ be admissible (in particular the provider is in the large-market setting). For every telehealth commitment $\theta\in[0,1]$, there is an equilibrium in which patients mix among balking, the office and telehealth (all three proportions positive) if and only if
--   $$\theta\in(\theta^T,\theta^O).$$
--
--   This identifies the middle region of Figure 3, in which both channels are used.
--
--   **Formalization Note** "Equilibrium" is the predicate of the definition `TelehealthParity.Access.Equilibrium`; $\theta^T,\theta^O$ are (11)–(12).
-- source:
--   Çakıcı and Mills, Telehealth in Acute Care: Pay Parity and Patient Access, SSRN working paper (version of August 19, 2024), p. 14, Theorem 1; proof Appendix C, EC p. 4 (PDF 37)

import Mathlib
import Definitions.Def_TelehealthParity_Access_Setting
import Definitions.Def_TelehealthParity_Access_Equilibrium

namespace TelehealthParity.Access

theorem theorem_1 (p : Params) (hp : p.Standing) (q : ℝ) (hq : Admissible p q)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    IsBOT p q θ ↔ θ ∈ Set.Ioo (thetaT p q) (thetaO p q) := by sorry

end TelehealthParity.Access
