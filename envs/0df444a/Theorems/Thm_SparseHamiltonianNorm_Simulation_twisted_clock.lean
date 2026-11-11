-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_twisted_clock
-- name    : SparseHamiltonianNorm.Simulation.twisted_clock
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:57.961325+00:00
-- url     : https://prove2.me/theorems/5e37745c-2310-462c-865b-bffd87894521
-- title:
--   Lemma 14 — Phase-twisted input-output clock realization
-- statement:
--   Under the standing assumptions of Eq. (61), let $m,p$ be positive integers and let $a,b,\lambda$ be defined by Eqs. (73)–(75) on horizon $R=3mp-p$. Then
--   $$\sum_{j=0}^{R-1}|a_j|^2=\sum_{j=0}^{R-1}|b_j|^2=1,\qquad1\le\lambda\le2,$$
--   $$P_{b\leftarrow a}(1)=J_b^\dagger\mathcal R_R(1)J_a=\widetilde U_{m,p}/\lambda.$$
--   The scheduled block uses exactly $R=3mp-p$ Cayley calls. The two clock vectors have different phase placements; their shared normalization and the signed operator integral are conclusions rather than model assumptions.
--
--   Differences from the source:
--   - encoding: integer coefficient sums, clock Euclidean norms, and one call per slot → finite full-support sums, squared Euclidean norms equal to one, and the length of the explicitly scheduled interaction list; reason: zero extension, positivity of m and p, and the actual routed call at every slot make the encodings equivalent
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 14, p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=23; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_PhaseKernel

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
/-- Li--Wang, Lemma 14, p.23, Eq. (77), and the exact per-block Cayley count on p.24. -/
theorem twisted_clock (n e d m p : ℕ) (Λ t L₀ : ℝ)
    (V : Matrix (Fin e) (Fin n) ℂ) (M : Matrix (Fin e) (Fin e) ℂ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (hp : 1 ≤ p) (hΛ : 0 < Λ) (ht : 0 ≤ t)
    (hV : V.conjTranspose * V = 1) (hM : M.IsHermitian)
    (hMoment : CompressedMoment V M) (hL : max 1 (opNorm M) ≤ L₀) :
    clockNormSq (inputClock m p) = 1 ∧ clockNormSq (outputClock m p) = 1 ∧
    1 ≤ clockLambda m p ∧ clockLambda m p ≤ 2 ∧
    clockBlock d Λ t V M 1 (inputClock m p) (outputClock m p) =
      (1 / clockLambda m p : ℝ) • phaseIntegral d Λ t V M m p ∧
    routedCayleyCalls (clockHorizon m p) = 3 * m * p - p := by sorry
end SparseHamiltonianNorm.Simulation
