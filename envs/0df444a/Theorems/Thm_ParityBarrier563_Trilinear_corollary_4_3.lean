-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_corollary_4_3
-- name    : ParityBarrier563.Trilinear.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:00.356089+00:00
-- url     : https://prove2.me/theorems/8b5e1922-2ea0-41a2-ab2a-c8e27f81e6b4
-- title:
--   Corollary 4.3 — a per-test tail bound gives corr_b(ψ) ≤ 2^{κ|V|}ε except with probability 2^{(|V|+1)L}δ
-- statement:
--   Let $V$ be a finite set of variables, $b\ge1$, $0<\kappa\le1$ and $L\ge1$ (a real number), and suppose that every $b$-CNF on $\{0,1\}^V$ is a sum of at most $2^{\kappa|V|}$ functions $\mathrm{cl}_b(S)$ with $|S|\le L$. Let $\psi$ be a random function $\{0,1\}^V\to[-1,1]$ such that, for some numbers $\varepsilon,\delta>0$ and **every** function $J:\{0,1\}^V\to\{0,1\}$,
--
--   $$\Pr\bigl[\,|\mathbb E[\psi J]|>\varepsilon\,\bigr]\le\delta .$$
--
--   Then
--
--   $$\Pr\bigl[\,\mathrm{corr}_b(\psi)>2^{\kappa|V|}\varepsilon\,\bigr]\le2^{(|V|+1)L}\,\delta .$$
--
--   This is the union bound that turns moment estimates for a single test into a bound against all $b$-CNFs at once.
--
--   Differences from the source:
--   - encoding: a random function {0,1}^V → [−1,1] → a family ψ_ω on an arbitrary probability space (Ω, μ), measurable in ω at each point, with values in [−1,1]; probabilities are μ.real; reason: no law is specified in the source; this covers every law
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Corollary 4.3, printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation
open MeasureTheory

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Corollary 4.3, printed p.15 / PDF 17. The random function `ψ` lives on an arbitrary
probability space `(Ω, μ)`. -/
theorem corollary_4_3 (V : Type) [Fintype V] [DecidableEq V] (b : ℕ) (κ L : ℝ)
    (hb : 1 ≤ b) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L)
    (hdec : HasClosureDecomp b V ((2 : ℝ) ^ (κ * Fintype.card V)) L)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ψ : Ω → RealFn V) (hψm : ∀ x, Measurable fun ω => ψ ω x)
    (hψ : ∀ ω x, ψ ω x ∈ Set.Icc (-1 : ℝ) 1)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hJ : ∀ J : BoolFn V, μ.real {ω | ε < |avg (fun x => ψ ω x * ind J x)|} ≤ δ) :
    μ.real {ω | ¬ corr b (ψ ω) ≤ (2 : ℝ) ^ (κ * Fintype.card V) * ε} ≤
      (2 : ℝ) ^ (((Fintype.card V : ℝ) + 1) * L) * δ := by sorry

end ParityBarrier563.Trilinear
