-- Prove2me | Theorems.Thm_ShockWear_WearProcess_theorem410
-- name    : ShockWear.WearProcess.theorem410
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:56:08.287582+00:00
-- url     : https://prove2.me/theorems/791b1f37-546c-4f14-b4f6-cf626b9f8323
-- title:
--   Theorem 4.10 — the first passage time of a nondecreasing Markov wear process above a fixed level is IHRA
-- statement:
--   Let $\{Z(t),t\ge0\}$ be the wear accumulated by a device in $[0,t]$, and suppose that
--
--   1. (4.8) $Z(0)=0$ and $Z(t+\Delta)-Z(t)\ge0$ for all $t,\Delta\ge0$, with probability one;
--   2. (4.9) $\{Z(t),t\ge0\}$ is a Markov process;
--   3. (4.10) $P\{Z(t+\Delta)-Z(t)\le u\mid Z(t)=z\}$ is decreasing in both $z$ and $t$ in the region $t\ge0$, $z\ge0$, $\Delta\ge0$.
--
--   For a level $x$ let $T_x=\inf\{t:Z(t)>x\}$ be the first passage time of the wear above $x$, and $\bar H_x(t)=P\{T_x>t\}$ its survival function. Then $T_x$ has an IHRA distribution:
--
--   $$
--   t\longmapsto\big[\bar H_x(t)\big]^{1/t}\quad\text{is decreasing on } t>0 .
--   $$
--
--   If a device fails when its accumulated wear first exceeds its capacity $x$, its failure time is $T_x$; the theorem says that its life distribution has increasing hazard rate average under no assumption on the law of the wear beyond (4.8)–(4.10). The conditions hold, for example, when the paths start at $0$ and the increments are nonnegative, stationary and independent (compound Poisson processes).
--
--   **Formalization Note** (4.8) is read pathwise: almost every path starts at $0$ and is nondecreasing (the paper's "with probability one" is ambiguous in quantifier order). (4.9) is the Markov property for the natural filtration. (4.10) is imposed on an explicit version $\kappa_{t,\Delta}$ of the conditional law of the increment given $Z(t)$, which agrees a.e. with Mathlib's `condDistrib`. $T_x$ takes values in $[0,\infty]$ and may be infinite with positive probability; $\bar H_x(t)=1$ for $t<0$. The level $x$ is any real number (for $x<0$ the statement holds trivially).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 641, Theorem 4.10 (conditions (4.8)–(4.10), pp. 640–641; IHRA, p. 631 (iv))

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem theorem410 {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω) [IsProbabilityMeasure pr]
    (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ) (hZ : IsWearProcess pr Z κ) (x : ℝ) :
    IsIHRA (passSurv pr Z x) := by sorry

end ShockWear.WearProcess
