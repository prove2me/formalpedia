-- Prove2me | Theorems.Thm_QubitFreqSensing_lemma_5_6
-- name    : QubitFreqSensing.lemma_5_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:21:55.657806+00:00
-- url     : https://prove2.me/theorems/064ef65c-c59f-4372-9eeb-278cd9be67ff
-- title:
--   Lemma 5.6 — $\int_0^{2\pi}|\cos(\omega x)|\,dx\ge\pi-1$
-- statement:
--   For every $\omega>0$,
--
--   $$
--   \int_0^{2\pi}|\cos(\omega x)|\,dx\ \ge\ \pi-1 .
--   $$
--
--   This bound gives the lower estimate $(\pi-1)/(2\pi)-1/(2C)>1/8$ on the slope of $z\mapsto\langle g_i,\Phi^{(i)}_zu\rangle$ at $0$ in the proof of Lemma 5.9.
--
--   Differences from the source: none.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Lemma 5.6, p.18 (PDF p.18)

import Mathlib

open Real

namespace QubitFreqSensing

/-- **Lemma 5.6** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), Lemma 5.6,
p.18). "For all ω > 0, we have ∫_0^{2π} |cos(ωx)|dx ≥ π − 1." -/
theorem lemma_5_6 (ω : ℝ) (hω : 0 < ω) :
    π - 1 ≤ ∫ x in (0 : ℝ)..2 * π, |Real.cos (ω * x)| := by sorry

end QubitFreqSensing
