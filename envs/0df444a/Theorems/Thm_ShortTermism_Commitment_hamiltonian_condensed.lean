-- Prove2me | Theorems.Thm_ShortTermism_Commitment_hamiltonian_condensed
-- name    : ShortTermism.Commitment.hamiltonian_condensed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:46.573993+00:00
-- url     : https://prove2.me/theorems/3255282c-8f97-453b-9bf5-2a382b7bc641
-- title:
--   §A.2.1, pp. 46–47 — the HJB (18) integrand in condensed form with Â, B̂, D̂
-- statement:
--   In the setting of the mission's model, let $H_C(\delta,a,e,f_1,f_2)$ be the braces of the HJB equation (18) for coupon $C$, firm size $\delta$, efforts $(a,e)$ and slopes $f_1=f'(\delta)$, $f_2=f''(\delta)$, and let $\hat A,\hat B,\hat D$ be the condensed coefficients of Appendix A.2.1 (functions of $\delta$). Then for all real $C,\delta,a,e,f_1,f_2$,
--   $$H_C(\delta,a,e,f_1,f_2)=\delta\Big(af_1+e-\frac{a^2\hat A}{2}-\frac{e^2\hat D}{2}-ae\hat B\Big)+\delta\psi-(1-\tau)C+\phi\delta f_1+\tfrac12\sigma_\delta^2\delta^2 f_2 .$$
--
--   This is the algebraic identity behind the paper's sentence "The optimization on the RHS of the HJB (18) can be rewritten as $\max\{af'(\delta)+e-\tfrac12a^2\hat A-\tfrac12e^2\hat D-ae\hat B\}$": since $\delta>0$, the efforts that maximize the braces of (18) are exactly those that maximize the condensed objective. It is the form in which every effort-policy argument of the paper, including the proof of Proposition 5, is carried out.
--
--   **Formalization Note** The page displays only the effort-dependent part and omits the positive factor $\delta$ and the terms $\delta\psi-(1-\tau)C+\phi\delta f'(\delta)+\tfrac12\sigma_\delta^2\delta^2f''(\delta)$; the statement restores them, so it is an exact identity. The page's range "$a\in[a,\bar a]$" is a typo for $a\in[0,\bar a]$; the identity itself holds without any range. The standing assumptions are carried as a hypothesis for uniformity.
-- source:
--   Hackbarth, Rivera & Wong, Optimal Short-Termism, ECGI Finance Working Paper 546/2018 (June 2021 version, SSRN 3060869), pp. 46–47 (PDF 50–51), Appendix A.2.1, display defining Â, D̂, B̂

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model

namespace ShortTermism.Commitment

theorem hamiltonian_condensed (P : Params) (hP : P.Standing) (C δ a e f1 f2 : ℝ) :
    hjbIntegrand P C δ a e f1 f2
      = δ * condensedObj P δ a e f1 + δ * P.ψ - (1 - P.τ) * C + P.φ * δ * f1
        + 1 / 2 * P.σδ ^ 2 * δ ^ 2 * f2 := by sorry

end ShortTermism.Commitment
