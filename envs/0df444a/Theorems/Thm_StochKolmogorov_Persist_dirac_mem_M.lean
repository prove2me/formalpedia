-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_dirac_mem_M
-- name    : StochKolmogorov.Persist.dirac_mem_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:50.348982+00:00
-- url     : https://prove2.me/theorems/29423352-a196-47e0-9e6f-c4658561e546
-- title:
--   §1.1, p. 5 — the Dirac measure δ* at 0 is an ergodic invariant probability measure on ∂ℝⁿ₊, so M ≠ ∅
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force.
--
--   The Dirac measure $\delta^*$ at the origin $0\in\mathbb R^n_+$ belongs to $\mathcal M$: it is an invariant probability measure of $X$, it is ergodic (extremal among invariant probability measures), and it is supported on the boundary $\partial\mathbb R^n_+$. In particular $\mathcal M\ne\emptyset$.
--
--   This guarantees that Assumption 1.2, a condition on $\mathrm{Conv}(\mathcal M)$, is never vacuous: it always requires at least $\max_i\lambda_i(\delta^*)=\max_i\big(f_i(0)-\sigma_{ii}g_i^2(0)/2\big)>0$.
--
--   **Formalization Note** The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, p. 5 ("Note that if we let δ* be the Dirac measure concentrated at 0 then δ* ∈ M so that M ≠ ∅.")

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- §1.1, p. 5: the Dirac measure `δ*` at `0` is an ergodic invariant probability measure on
`∂ℝⁿ₊`, so `M ≠ ∅`. -/
theorem dirac_mem_M {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    Measure.dirac (0 : SDEState n) ∈ bdryErgodic P X := by sorry

end StochKolmogorov.Persist
