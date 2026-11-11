-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_D_4
-- name    : TwoItemMenu1393.Main.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:29:48.368167+00:00
-- url     : https://prove2.me/theorems/4dc372cb-4513-4366-b57b-33ca1b680920
-- title:
--   Lemma D.4 — Weak derivative estimate
-- statement:
--   There is an absolute positive constant $C$ such that for every compactly supported $\Phi\in W^{1,2}(\mathbb R^2;\mathbb R^2)$ with integrable $\mathcal T(D\Phi)$, and every $\alpha>0$,
--   $$\operatorname{Leb}\{v:\|D\Phi(v)\|>\alpha\}\le\frac{C}{\alpha}\int_{\mathbb R^2}\|\mathcal T(D\Phi(v))\|\,dv.$$
--   The derivative has the Euclidean operator norm and $\mathcal T$ has the Euclidean vector norm. Weak derivatives are actual distributional derivatives; no differentiability or smoothness of $\Phi$ is required. The estimate controls exceptional derivative area in the allocation convergence argument.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: membership in W¹,² and weak derivative DΦ → square-integrable representatives Φ,J and integration by parts against every compactly supported smooth test function; reason: this is the usual definition of the first weak derivative, with no extra regularity on Φ
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma D.4, p. 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=29

import Definitions.Def_TwoItemMenu1393_Main_Fields
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma D.4, p. 29.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_D_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : Vec → Vec) (J : Vec → Mat),
      HasCompactSupport Φ → Sobolev12 Φ J → Integrable (fun v => scalarDeviation (J v)) →
      ∀ α : ℝ, 0 < α →
        volume {v | α < ‖J v‖} ≤
          ENNReal.ofReal ((C/α) * ∫ v, ‖scalarDeviation (J v)‖) := by sorry

end TwoItemMenu1393.Main
