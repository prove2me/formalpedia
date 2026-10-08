-- Prove2me | Theorems.Thm_TDApprox_Conv_section6_A_negDef
-- name    : TDApprox.Conv.section6_A_negDef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:47.441044+00:00
-- url     : https://prove2.me/theorems/e1085144-19f6-4783-89da-f09dd565d01b
-- title:
--   §6, p. 19 — A = E₀[A(X_t)] and b = E₀[b(X_t)] are finite, Ar* + b = 0, and A is negative definite
-- statement:
--   Under Assumptions 1 and 2, let $\lambda \in [0,1]$, let $X_t = (i_t,i_{t+1},z_t)$ be the steady-state process of §5, and for $X = (i,j,z)$ let
--   $$A(X) = z\big(\alpha\phi'(j) - \phi'(i)\big), \qquad b(X) = z\,g(i,j),$$
--   so that the TD($\lambda$) step is $s(r,X) = A(X)r + b(X)$. Let $r^*$ satisfy $\Pi T^{(\lambda)}(\Phi'r^*) = \Phi'r^*$ (Lemma 5). Then $A = E_0[A(X_t)]$ and $b = E_0[b(X_t)]$ are well defined and finite,
--   $$Ar^* + b = 0,$$
--   and $A$ is negative definite: $v'Av < 0$ for every $v \ne 0$.
--
--   These are conditions (c) and (d) of Theorem 2 for TD($\lambda$), and they identify $r^*$ as the root to which Theorem 2 drives the iterates.
--
--   **Formalization Note.** The page derives $(r-r^*)'A(r-r^*) < 0$ for every $r \ne r^*$ and concludes that $A$ is negative definite; the Lean statement gives the conclusion in the form $v'Av < 0$ for all $v \ne 0$, which is the same claim with $v = r - r^*$.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), §6, pp. 18–19 ("By Lemma 6, A ≜ E₀[A(X_t)] …, and thus A is negative definite")

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **§6, p. 19** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996)): with `A(X) = z(αφ′(j) − φ′(i))` and
`b(X) = z g(i, j)` for `X = (i, j, z)`, under Assumptions 1 and 2, for the steady-state process
`X_t`, `λ ∈ [0, 1]` and `r*` the fixed point of Lemma 5, the means `A = E_0[A(X_t)]` and
`b = E_0[b(X_t)]` are well defined and finite, `A r* + b = 0`, and `A` is negative definite. -/
theorem section6_A_negDef {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i)
    (rstar : Fin K → ℝ) (hfix : proj π φ (Tlam P g α lam (Jtilde φ rstar)) = Jtilde φ rstar) :
    ∀ t : ℤ,
      (∀ k l, Integrable (fun ω => Amat α φ (Xstat α lam φ i t ω) k l) μ) ∧
      (∀ k, Integrable (fun ω => bvec g (Xstat α lam φ i t ω) k) μ) ∧
      (fun k l => ∫ ω, Amat α φ (Xstat α lam φ i t ω) k l ∂μ) *ᵥ rstar +
          (fun k => ∫ ω, bvec g (Xstat α lam φ i t ω) k ∂μ) = 0 ∧
      ∀ v : Fin K → ℝ, v ≠ 0 →
        v ⬝ᵥ ((fun k l => ∫ ω, Amat α φ (Xstat α lam φ i t ω) k l ∂μ) *ᵥ v) < 0 := by sorry

end TDApprox.Conv
