-- Prove2me | Theorems.Thm_Teletriage_OneShot_proposition_3
-- name    : Teletriage.OneShot.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:07.225995+00:00
-- url     : https://prove2.me/theorems/1289e597-29c2-4de1-8374-66b387b44ac4
-- title:
--   Proposition 3, p. 11 (PDF 11) — with Uniform[l,u] beliefs and b̲0 < l < b0 < u < b̄0, teletriage cuts ED usage iff β < β⁰ and double-dipping iff α < α⁰
-- statement:
--   Consider the one-shot open-access model under the standing assumptions, with informative teletriage ($\alpha+\beta<1$, as in Proposition 2). Suppose that beliefs are uniformly distributed on $[l,u]\subseteq[0,1]$, with density $f(b)=1/(u-l)$ for $l<b<u$, and that
--   $$\underline b_0<l<b_0<u<\bar b_0,$$
--   so that with teletriage every patient calls before visiting a provider, while without it some patients go to the PCP and some to the ED. Let $\pi^{ED},\tilde\pi^{ED}$ be the overall probabilities of ED usage and $\pi^{DD},\tilde\pi^{DD}$ those of double-dipping, without and with teletriage. Then
--   $$\pi^{ED}-\tilde\pi^{ED}>0\iff\beta<\beta^0=\frac{u-\frac{u^2}{2}-\bigl(b_0-\frac{b_0^2}{2}\bigr)}{u-\frac{u^2}{2}-\bigl(l-\frac{l^2}{2}\bigr)},\tag{15}$$
--   $$\pi^{DD}-\tilde\pi^{DD}>0\iff\alpha<\alpha^0=\frac{b_0^2-l^2}{u^2-l^2}.\tag{16}$$
--
--   Teletriage thus reduces unnecessary ED usage exactly when the overtriage rate is low enough, and reduces double-dipping exactly when the undertriage rate is low enough.
--
--   **Formalization Note** Informativeness $\alpha+\beta<1$ is inherited from Proposition 2, in whose setting $\underline b_0,\bar b_0$ are defined. $[l,u]\subseteq[0,1]$ is $0\le l$, $u\le1$. The overall probabilities are averages $\frac1{u-l}\int_l^u$ of the per-belief probabilities, which are computed from the patients' optimal actions (argmin of (1) and (11), ties ED ≻ teletriage ≻ PCP), not from the closed forms of p. 11.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. 11 (PDF 11), Proposition 3, (15), (16)

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Proposition 3, p. 11: with beliefs Uniform on `[l, u] ⊆ [0, 1]` and `b̲0 < l < b0 < u < b̄0`,
teletriage strictly lowers overall ED usage iff `β < β⁰`, (15), and strictly lowers
double-dipping iff `α < α⁰`, (16). -/
theorem proposition_3 (P : Params) (hS : P.Standing) (hI : P.Informative) (l u : ℝ)
    (hl : 0 ≤ l) (hu : u ≤ 1)
    (h1 : bLow P < l) (h2 : l < b0 P) (h3 : b0 P < u) (h4 : u < bHigh P) :
    (0 < avg (piED P) l u - avg (piEDtt P) l u ↔ P.β < betaSup0 P l u) ∧
    (0 < avg (piDD P) l u - avg (piDDtt P) l u ↔ P.α < alphaSup0 P l u) := by sorry

end Teletriage.OneShot
