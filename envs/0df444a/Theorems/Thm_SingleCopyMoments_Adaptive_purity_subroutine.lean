-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_purity_subroutine
-- name    : SingleCopyMoments.Adaptive.purity_subroutine
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:46:25.456381+00:00
-- url     : https://prove2.me/theorems/48bc6d26-a1f1-4c2b-8bb8-fafe1c182bfe
-- title:
--   Lemma 20 — Additive-error purity estimation
-- statement:
--   For every fixed accuracy $\varepsilon\in(0,1)$ and failure tolerance $\delta\in(0,1)$ there is a constant $C_{\varepsilon,\delta}>0$ such that, for every dimension $D\ge1$, one single-copy protocol with a natural worst-case budget $T$ satisfies
--
--   $$T\le C_{\varepsilon,\delta}\sqrt D,\qquad\Pr_\rho\{|\widehat p_2-\operatorname{Tr}(\rho^2)|\le\varepsilon\}\ge1-\delta\quad\text{for every state }\rho.$$
--
--   Only classical information passes between copies. This supplies the base estimation rate, including the one-dimensional case. The notation for estimability expands to the displayed uniform operational claim.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: the asymptotic square-root rate, including the immediate D=1 case → one bound over every positive dimension; reason: the source proof covers D=1 separately and permits enlarging its dimension-independent constant
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 20, printed p. 21 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation

open scoped Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 20, printed p.21 (PDF p.23); positive dimensions including D=1. -/
theorem purity_subroutine : Estimable 2 (1/2) := by sorry

end SingleCopyMoments.Adaptive
