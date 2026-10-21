-- Prove2me | Theorems.Thm_SingCtrlLevy_Barrier_lemma_2
-- name    : SingCtrlLevy.Barrier.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:24.48821+00:00
-- url     : https://prove2.me/theorems/315f111b-09a8-49cf-a14c-2b0d87647cfb
-- title:
--   Lemma 2, p. 6 — every barrier strategy π^b is admissible
-- statement:
--   Let $X$ be a Lévy process with triplet $(\gamma,\sigma,\Pi)$ satisfying Assumption 2 (it is not a driftless compound Poisson process, and $\int_{\mathbb R\setminus(-1,1)}e^{\bar\theta|z|}\Pi(dz)<\infty$ for some $\bar\theta>0$), let $q>0$, and let the running cost $f$ and unit cost $C$ satisfy Assumption 1. For every barrier $b\in\mathbb R$ and every starting point $x\in\mathbb R$, the barrier strategy $R^b_t=-\inf_{s\in[0,t]}\{(x+X_s-b)\wedge0\}$ is a strategy and satisfies the integrability condition (2.4):
--   $$\mathbb E_x\Big[\int_0^\infty e^{-qt}|f(U^b_t)|\,dt+\int_{[0,\infty)}e^{-qt}\,dR^b_t\Big]<\infty .$$
--   Hence $\pi^b$ is admissible, and $v^{(1)}_b(x)$, $v^{(2)}_b(x)$ are finite.
--
--   **Formalization Note** Admissibility is from the given start $x$ (the barrier strategy itself depends on $x$). Assumption 2(i) is a standing hypothesis of §§2–4 and is carried here.
-- source:
--   Noba & Yamazaki, On Singular Control for Lévy Processes, arXiv:2008.03021v3, p. 6, Lemma 2

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_SingCtrlLevy_Barrier_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace SingCtrlLevy.Barrier

theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (T : Triplet) (hX : IsLevyWith P X T)
    (f : ℝ → ℝ) (q C : ℝ) (hq : 0 < q) (hA1 : Assumption1 f C q) (hA2 : Assumption2ii T)
    (hA2i : ¬ T.DriftlessCP)
    (x b : ℝ) :
    IsAdmissible P X f q x (barrierR X x b) := by sorry

end SingCtrlLevy.Barrier
