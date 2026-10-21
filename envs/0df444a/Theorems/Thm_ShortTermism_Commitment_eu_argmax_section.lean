-- Prove2me | Theorems.Thm_ShortTermism_Commitment_eu_argmax_section
-- name    : ShortTermism.Commitment.eu_argmax_section
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:04.40866+00:00
-- url     : https://prove2.me/theorems/c5a593b4-68c9-4671-849c-b64cadd8b36f
-- title:
--   Proof of Proposition 5, §A.4.2, p. 49 — e_u(δ) maximizes the e-section of the condensed objective at every slope
-- statement:
--   In the setting of the mission's model, assume the standing assumptions, let $f_u$ be the unlevered value solving (25) with the conditions of Proposition 3, and let $(a_u,e_u)$ be its effort policy: for every $\delta\ge\underline\delta$, $(a_u(\delta),e_u(\delta))\in[0,\bar a]\times[0,\bar e]$ maximizes the braces of (25) at $f_u'(\delta),f_u''(\delta)$ over that box. Then for every $\delta\ge\underline\delta$ and **every** real slope $f_1$, $e_u(\delta)\in[0,\bar e]$ and
--   $$e_u(\delta)\in\arg\max_{e\in[0,\bar e]}\Big\{a_u(\delta)f_1+e-\frac{a_u(\delta)^2\hat A}{2}-\frac{e^2\hat D}{2}-a_u(\delta)\,e\,\hat B\Big\}.$$
--
--   The point is the change of slope: $e_u$ is defined through the unlevered slope $f_u'(\delta)$, but the conclusion holds at any slope $f_1$, in particular at the levered slope $f'(\delta)$. This is the step in the proof of Proposition 5 that transfers the unlevered short-term effort to the levered problem once long-term effort is fixed at $a_u(\delta)$.
--
--   **Formalization Note** The page writes "$\arg\max_{a,e}$" without bounds; the maximization is over the effort box $[0,\bar a]\times[0,\bar e]$ of Definition 1 and Appendix A.2.1, and the conclusion's $\arg\max_e$ is over $[0,\bar e]$, the range of the no-underinvestment problem (A.29). No concavity of the objective is assumed.
-- source:
--   Hackbarth, Rivera & Wong, Optimal Short-Termism, ECGI Finance Working Paper 546/2018 (June 2021 version, SSRN 3060869), pp. 48–49 (PDF 52–53), Appendix A.4.2, proof of Proposition 5, display 'which implies that e_u(δ) ∈ arg max_e …'

import Mathlib
import Definitions.Def_ShortTermism_Commitment_Model

namespace ShortTermism.Commitment

theorem eu_argmax_section (P : Params) (hP : P.Standing) (fu au eu : ℝ → ℝ)
    (hv : IsUnleveredValue P fu) (hu : IsUnleveredPolicy P fu au eu)
    (δ : ℝ) (hδ : P.dlow ≤ δ) (f1 : ℝ) :
    eu δ ∈ Set.Icc 0 P.ebar ∧
      ∀ e ∈ Set.Icc 0 P.ebar, condensedObj P δ (au δ) e f1 ≤ condensedObj P δ (au δ) (eu δ) f1 := by sorry

end ShortTermism.Commitment
