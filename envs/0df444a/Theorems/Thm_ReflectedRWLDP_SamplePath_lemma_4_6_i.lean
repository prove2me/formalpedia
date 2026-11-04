-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_6_i
-- name    : ReflectedRWLDP.SamplePath.lemma_4_6_i
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T20:47:50.413428+00:00
-- url     : https://prove2.me/theorems/52edd927-f7f4-4331-9f66-3576a2589bdc
-- title:
--   Lemma 4.6 (i), p. 22 — $\limsup_{x\to\infty}\frac1x\log P_{xy}(T_1/x>T)\le ty+T\log\mathbf E e^{tU}$ (4.5)
-- statement:
--   Let $U_1,U_2,\dots$ satisfy the standing assumptions of the paper (i.i.d., $\mathbf E U<0$, Assumptions 2.1–2.3, $p>0$), and let $X$ be the reflected random walk $X_{k+1}=[X_k+U_{k+1}]^+$ started at $X_0=xy$; write $\mathbf P_{xy}$ for its law and $T_1=\inf\{k>0:X_k=0\}$ for its first return time to $0$. Then for any $t,y\ge 0$ and $T>0$,
--   $$\limsup_{x\to\infty}\frac1x\log\mathbf P_{xy}\big(T_1/x>T\big)\le ty+T\log\mathbf E e^{tU}. \tag{4.5}$$
--   The limit is over real $x\to\infty$; $\log 0=-\infty$ and the right-hand side is read in $[-\infty,\infty]$ (it is $+\infty$ if $\mathbf E e^{tU}=\infty$).
--
--   This is part (i) of Lemma 4.6, a Chernoff-type estimate on the duration of a busy period started from a high level; part (ii), the bound (4.6), is `ReflectedRWLDP.SamplePath.lemma_4_6_ii`.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 22–23, Lemma 4.6 (i), (4.5); proof p. 23

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath

/-- **Lemma 4.6 (i)** (pp. 22–23), bound (4.5). For the reflected random walk started at `xy`,
`limsup_{x→∞} x⁻¹ log P_{xy}(T₁/x > T) ≤ t y + T log E e^{tU}` for all `t, y ≥ 0`, `T > 0`. -/
theorem lemma_4_6_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) :
    ∀ t y T : ℝ, 0 ≤ t → 0 ≤ y → 0 < T →
      limsup (fun x : ℝ => speedLog x
          (P {ω | ENNReal.ofReal (x * T) <
            ENat.toENNReal (retTime (fun k => lindley (x * y) U k ω) 1)})) atTop ≤
        ((t * y : ℝ) : EReal) + (T : EReal) * BellWilliams2001.ThresholdPolicy.logMGF P (U 0) t := by sorry

end ReflectedRWLDP.SamplePath
