-- Prove2me | Theorems.Thm_SpedalieriQHT_eq_19
-- name    : SpedalieriQHT.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:51.727413+00:00
-- url     : https://prove2.me/theorems/933bef97-bc50-44d5-aa64-51e1f9175457
-- title:
--   Eq. (19) — closed form of the fidelity bound $H_F(r)$
-- statement:
--   Let $F\ge 0$ and $r$ be real numbers, and let
--   $$
--   H_F(r)=\sup_{0\le s<1}\frac{-r s-\ln F}{1-s}
--   $$
--   be the fidelity bound, with $\ln 0=-\infty$. Then
--   $$
--   H_F(r)=\begin{cases}\ln\dfrac1F, & r\ge\ln\dfrac1F,\\[2mm] +\infty, & r<\ln\dfrac1F,\end{cases}
--   $$
--   where $\ln(1/0)=+\infty$, so that $H_F(r)=+\infty$ for every $r$ when $F=0$.
--
--   The closed form shows that the fidelity bound depends only on the comparison between the rate $r$ and $\ln(1/F)$.
--
--   **Formalization Note** $\ln(1/F)$ is written $-\operatorname{elog}F$ in `EReal`.
--
--   Differences from the source:
--   - generalization: $F$ the fidelity of two states, $F\in[0,1]$ → any real $F\ge 0$; reason: the maximization uses no upper bound on $F$, and fidelities are a special case
--   - generalization: $r>0$ (Eq. (13)) → every real $r$; reason: (18)–(19) hold for every real $r$, and the statement specializes to $r>0$
--   - encoding: $\ln$, $\ln(1/F)$, $+\infty$ → `EReal` with $\ln 0=-\infty$ (`elog`) and $\ln(1/F)=-\operatorname{elog}F$; reason: Lean convention; same instances, including $\ln(1/0)=+\infty$
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eq. (19), p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_SpedalieriQHT_fidelityBound

open HayashiHoeffding (elog)

namespace SpedalieriQHT

/-- **Eq. (19).** For every `F ≥ 0` and every real `r`, the fidelity bound
`H_F(r) = sup_{0≤s<1} (−r s − ln F)/(1 − s)` equals `ln(1/F)` when `r ≥ ln(1/F)` and `+∞`
when `r < ln(1/F)`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, Eq. (19), p.3: "After a simple calculation
we find H_F(r) = ln 1/F, for r ≥ ln 1/F ; +∞, for r < ln 1/F".

**Formalization Note.** `ln(1/F)` is `-elog F` in `EReal`, which is `+∞` at `F = 0`; then the
condition `r ≥ +∞` fails and the value is `+∞`, the paper's `ln(1/0) = +∞`. The statement is
made for every `F ≥ 0`, not only for fidelities `F ∈ [0, 1]`. -/
theorem eq_19 (F : ℝ) (hF : 0 ≤ F) (r : ℝ) :
    fidelityBound F r = if -elog F ≤ (r : EReal) then -elog F else ⊤ := by sorry

end SpedalieriQHT
