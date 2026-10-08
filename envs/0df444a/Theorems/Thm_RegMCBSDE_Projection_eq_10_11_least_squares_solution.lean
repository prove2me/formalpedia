-- Prove2me | Theorems.Thm_RegMCBSDE_Projection_eq_10_11_least_squares_solution
-- name    : RegMCBSDE.Projection.eq_10_11_least_squares_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:17.718343+00:00
-- url     : https://prove2.me/theorems/767dc1cc-b479-4243-866f-455e3a96972d
-- title:
--   Proof of Theorem 2, Eqs. (10)–(11) — the least-squares problem (9) is solved by L2 projections
-- statement:
--   Assume (H1)–(H2) and the standing model, let the bases have invertible Gram matrices, and let $\alpha$ be a projection–Picard scheme with $I$ iterations. Write $h=T/N$. Then for every Picard step $i\ge1$ and every $0\le k\le N-1$, almost surely:
--
--   1. for $1\le l\le q$, whenever $Y^{N,I,I}_{t_{k+1}}\Delta W_{l,k}$ is square integrable,
--   $$Z^{N,i,I}_{l,t_k}=\frac1h\,\mathcal P_{p_{l,k}}\big(Y^{N,I,I}_{t_{k+1}}\Delta W_{l,k}\big);\tag{10}$$
--   2. $$Y^{N,i,I}_{t_k}=\mathcal P_{p_{0,k}}\Big(Y^{N,I,I}_{t_{k+1}}+h\,f\big(t_k,S^N_{t_k},Y^{N,i-1,I}_{t_k},Z^{N,i-1,I}_{t_k}\big)\Big).\tag{11}$$
--
--   These identities turn the least-squares definition of the scheme into the projection form on which every estimate of the proof of Theorem 2 rests: the $Z$-coefficients are a regression of $Y^{N,I,I}_{t_{k+1}}\Delta W_{l,k}$, and the $Y$-coefficients a Picard step composed with a projection.
--
--   **Formalization Note** The paper's projection $\mathcal P$ is defined on $\mathbf L_2(\Omega,\mathbb P)$, so (10) is stated for those $l$ for which the product $Y^{N,I,I}_{t_{k+1}}\Delta W_{l,k}$ is square integrable; the paper uses (10) without stating this. The argument of (11) is square integrable under the standing hypotheses.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 12, Proof of Theorem 2, Eqs. (10)–(11)

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Scheme

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, Eqs. (10)–(11)** (Gobet–Lemor–Warin, arXiv:math/0508491v1, p. 12): the
solution of the least-squares problem (9) is given by projections. For every Picard step
`i ≥ 1` and every `k < N`, with `h = T/N`:

* (10) for each component `m : Fin q` (the paper's `l = m + 1`),
  `Z^{N,i,I}_{l,t_k} = h⁻¹ 𝒫_{p_{l,k}}(Y^{N,I,I}_{t_{k+1}} ΔW_{l,k})`;
* (11) `Y^{N,i,I}_{t_k} = 𝒫_{p_{0,k}}(Y^{N,I,I}_{t_{k+1}} + h f(t_k, S^N_{t_k}, Y^{N,i-1,I}_{t_k}, Z^{N,i-1,I}_{t_k}))`,

almost surely. The paper's projection `𝒫` acts on `𝐋₂(Ω, P)`, so (10) is stated for the
components for which `Y^{N,I,I}_{t_{k+1}} ΔW_{l,k}` is square integrable (the paper uses (10)
without comment). The scheme is the relation (9) of `IsProjectionScheme`, not (10)–(11). -/
theorem eq_10_11_least_squares_solution (T : ℝ) (hT : 0 < T) {d q d' : ℕ}
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ → EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin q) ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ → EuclideanSpace ℝ (Fin q) → ℝ)
    (Cf L : ℝ) (hH1 : H1 T L b σ) (hH2 : H2 T Cf f)
    (S0 : EuclideanSpace ℝ (Fin d)) (N : ℕ) (hN : 0 < N)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ mΩ) (ΔW : ℕ → Ω → EuclideanSpace ℝ (Fin q))
    (PN : ℕ → Ω → EuclideanSpace ℝ (Fin d')) (ΦN : EuclideanSpace ℝ (Fin d') → ℝ)
    (hM : IsStandingModel P 𝓕 T N b σ S0 ΔW PN ΦN)
    (n : Fin (q + 1) → ℕ → ℕ)
    (p : (l : Fin (q + 1)) → (k : ℕ) → EuclideanSpace ℝ (Fin d') → Fin (n l k) → ℝ)
    (hp : IsBasis P N PN n p)
    (I : ℕ) (α : ℕ → (k : ℕ) → (l : Fin (q + 1)) → Fin (n l k) → ℝ)
    (hα : IsProjectionScheme P T N b σ f S0 ΔW PN ΦN p I α)
    (i : ℕ) (hi : 1 ≤ i) (k : ℕ) (hk : k < N) :
    (∀ m : Fin q,
        MemLp (fun ω => schemeY N PN ΦN p α I (k + 1) ω * ΔW k ω m) 2 P →
        (fun ω => schemeZ PN p α i k ω m) =ᵐ[P]
          fun ω => (T / N)⁻¹ * proj P (basisAt p PN m.succ k)
            (fun ω' => schemeY N PN ΦN p α I (k + 1) ω' * ΔW k ω' m) ω) ∧
      schemeY N PN ΦN p α i k =ᵐ[P]
        proj P (basisAt p PN 0 k) (fun ω => schemeY N PN ΦN p α I (k + 1) ω
          + (T / N) * f (gridTime T N k) (euler T N b σ S0 ΔW k ω)
              (schemeY N PN ΦN p α (i - 1) k ω) (schemeZ PN p α (i - 1) k ω)) := by sorry

end RegMCBSDE.Projection
