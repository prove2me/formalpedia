-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_sec_2_4_eq_2_6
-- name    : PrimalDualLDR.FixedRecourse.sec_2_4_eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:48.48208+00:00
-- url     : https://prove2.me/theorems/684220bf-2e7e-406b-99b0-884463b2ce00
-- title:
--   §2.4, (2.6), p. 7 — $\mathcal{SP}^l$ has the same optimal value as problem (2.6)
-- statement:
--   Assume the standing assumptions of §2. Then the dual linear-decision-rule problem
--   $$\mathcal{SP}^l:\quad \min_{x\in\mathcal L^2_{k,n},\,s\in\mathcal L^2_{k,m}} \mathbb E\big(c(\xi)^\top x(\xi)\big)\ \ \text{s.t.}\ \ \mathbb E\big([Ax(\xi)+s(\xi)-b(\xi)]\xi^\top\big)=0,\ s(\xi)\ge0\ \mathbb P\text{-a.s.}$$
--   and problem (2.6),
--   $$\min_{X,S}\ \operatorname{Tr}(MC^\top X)\ \ \text{s.t.}\ \ AX+S=B,\ \exists x\in\mathcal L^2_{k,n}: XM=\mathbb E(x(\xi)\xi^\top),\ \exists s\in\mathcal L^2_{k,m}: SM=\mathbb E(s(\xi)\xi^\top),\ s(\xi)\ge0\ \mathbb P\text{-a.s.},$$
--   have the same optimal value (in $[-\infty,+\infty]$, with $+\infty$ for an infeasible problem).
--
--   This is the first step of the tractable reformulation of the dual approximation: the infinite-dimensional decision rules $(x,s)$ are replaced by the finite-dimensional matrices $(X,S)$ determined by them through (2.5), and only a moment-feasibility condition on $S$ remains.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, §2.4, p. 7, (2.5)–(2.6) (unnumbered claim)

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- §2.4, (2.6), p. 7 (unnumbered): under the standing assumptions of §2, the dual linear-decision-rule
problem `SP^l` is equivalent to problem (2.6): their optimal values coincide. -/
theorem sec_2_4_eq_2_6 (σ : Setting) (hσ : σ.Standing) : σ.valSPl = σ.valLP26 := by sorry

end PrimalDualLDR.FixedRecourse
