-- Prove2me | Theorems.Thm_TDApprox_Conv_lemma_7
-- name    : TDApprox.Conv.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:35.090385+00:00
-- url     : https://prove2.me/theorems/5c3ddacc-04ad-4948-a7a9-2cea394ad461
-- title:
--   Lemma 7, p. 16 — E₀[s(r, X_t)] = ΦD(T^(λ)(Φ′r) − Φ′r)
-- statement:
--   Under Assumptions 1 and 2, let $(i_t)_{t\in\mathbb Z}$ be the chain in steady state, $\lambda \in [0,1]$, $z_t$ the eligibility vector of Eq. (5) and $X_t = (i_t,i_{t+1},z_t)$. For $X = (i,j,z)$ and $r \in \mathbb R^K$ let
--   $$s(r,X) = \big(g(i,j) + \alpha\phi(j)'r - \phi(i)'r\big)z$$
--   be the TD($\lambda$) step direction. Then, for every $t$ and every $r$, $E_0[s(r,X_t)]$ is well defined and finite, and
--   $$E_0[s(r,X_t)] = \Phi D\big(T^{(\lambda)}(\Phi'r) - \Phi'r\big).$$
--
--   In steady state, TD($\lambda$) therefore moves on average along $\Phi D(T^{(\lambda)}(\Phi' r) - \Phi' r)$, the direction of the deterministic iteration analysed in §3.
--
--   **Formalization Note.** $E_0[s(r,X_t)]$ is the expectation over the steady-state process. It is not defined by the right-hand side. $(\Phi D v)_k = \sum_i \pi(i)\phi_k(i)v(i)$, with the summability of these series stated as part of "well defined".
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Lemma 7, p. 16

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Lemma 7** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 16). Under Assumptions 1 and 2, for
the steady-state process `X_t = (i_t, i_{t+1}, z_t)`, `λ ∈ [0, 1]` and any `r ∈ ℝ^K`,
`E_0[s(r, X_t)] = ΦD(T^(λ)(Φ′r) − Φ′r)`, which is well defined and finite. -/
theorem lemma_7 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ)
    (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : ℤ → Ω → S) (hi : IsStationaryChain μ P π i) (r : Fin K → ℝ) :
    ∀ t : ℤ,
      Integrable (fun ω => sStep α g φ r (Xstat α lam φ i t ω)) μ ∧
      (∀ k, Summable (fun j => (π {j}).toReal * φ j k *
        (Tlam P g α lam (Jtilde φ r) j - Jtilde φ r j))) ∧
      ∫ ω, sStep α g φ r (Xstat α lam φ i t ω) ∂μ =
        fun k => ∑' j, (π {j}).toReal * φ j k * (Tlam P g α lam (Jtilde φ r) j - Jtilde φ r j) := by sorry

end TDApprox.Conv
