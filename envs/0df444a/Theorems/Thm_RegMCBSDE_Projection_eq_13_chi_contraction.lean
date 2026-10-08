-- Prove2me | Theorems.Thm_RegMCBSDE_Projection_eq_13_chi_contraction
-- name    : RegMCBSDE.Projection.eq_13_chi_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:41.627993+00:00
-- url     : https://prove2.me/theorems/cb494f22-776c-4232-a775-dff9d3925776
-- title:
--   Proof of Theorem 2, Step 2, Eq. (13) — χ^{N,I}_k is a (C_f h)-contraction on L2(F_k) with a unique fixed point
-- statement:
--   Assume (H1)–(H2) with constant $C_f$ and the standing model, let the bases have invertible Gram matrices, and let $\alpha$ be a projection–Picard scheme with $I$ iterations. Fix $0\le k\le N-1$, write $h=T/N$, and define on $\mathbf L_2(\mathcal F_k)$
--   $$\chi^{N,I}_k(Y)=\mathcal P_{p_{0,k}}\Big(Y^{N,I,I}_{t_{k+1}}+h\,f\big(t_k,S^N_{t_k},Y,Z^{N,I,I}_{t_k}\big)\Big).$$
--   Then:
--
--   1. for all $\mathcal F_k$-measurable square-integrable $Y_1,Y_2$,
--   $$\mathbb E|\chi^{N,I}_k(Y_2)-\chi^{N,I}_k(Y_1)|^2\le(C_fh)^2\,\mathbb E|Y_2-Y_1|^2;$$
--   2. if $C_fh<1$, there is an $\mathcal F_k$-measurable square-integrable $Y^{N,\infty,I}_{t_k}$ with
--   $$Y^{N,\infty,I}_{t_k}=\mathcal P_{p_{0,k}}\Big(Y^{N,I,I}_{t_{k+1}}+h\,f\big(t_k,S^N_{t_k},Y^{N,\infty,I}_{t_k},Z^{N,I,I}_{t_k}\big)\Big)\tag{13}$$
--   almost surely, and any two such fixed points agree almost surely.
--
--   The fixed point $Y^{N,\infty,I}_{t_k}$ is the limit of the Picard iterations at time $t_k$; the proof of Theorem 2 compares $Y^{N,I,I}_{t_k}$ with it.
--
--   **Formalization Note** The paper writes $Z^{N,i-1,I}_{t_k}$ inside $\chi^{N,I}_k$ and adds that $Z^{N,i,I}_{t_k}$ does not depend on $i\ge1$; as (13) shows, the intended argument is $Z^{N,I,I}_{t_k}$, which is what is formalized. The paper's "for $h$ small enough" is the contraction condition $C_fh<1$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 12, Proof of Theorem 2, Step 2, definition of χ^{N,I}_k and Eq. (13)

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Scheme

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, Step 2, Eq. (13)** (arXiv:math/0508491v1, p. 12). Fix `k < N`, put
`h = T/N` and
`χ^{N,I}_k(Y) = 𝒫_{p_{0,k}}(Y^{N,I,I}_{t_{k+1}} + h f(t_k, S^N_{t_k}, Y, Z^{N,I,I}_{t_k}))`.

* (a) For all `𝓕_k`-measurable square-integrable `Y₁, Y₂`,
  `𝔼|χ(Y₂) - χ(Y₁)|^2 ≤ (C_f h)^2 𝔼|Y₂ - Y₁|^2`, with `C_f` the constant of (H2).
* (b) If `C_f h < 1`, `χ` has a fixed point `Y^{N,∞,I}_{t_k} ∈ 𝐋₂(𝓕_k)`, i.e. (13)
  `Y^{N,∞,I}_{t_k} = 𝒫_{p_{0,k}}(Y^{N,I,I}_{t_{k+1}} + h f(t_k, S^N_{t_k}, Y^{N,∞,I}_{t_k}, Z^{N,I,I}_{t_k}))`
  almost surely, and it is unique up to almost-sure equality in `𝐋₂(𝓕_k)`.

The paper writes `Z^{N,i-1,I}_{t_k}` inside `χ` and adds that `Z^{N,i,I}` does not depend on
`i ≥ 1`; as (13) shows, it is `Z^{N,I,I}_{t_k}`. "For `h` small enough" is the contraction
condition `C_f h < 1`. -/
theorem eq_13_chi_contraction (T : ℝ) (hT : 0 < T) {d q d' : ℕ}
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
    (k : ℕ) (hk : k < N) :
    let χ : (Ω → ℝ) → Ω → ℝ := fun Y => proj P (basisAt p PN 0 k) (fun ω =>
      schemeY N PN ΦN p α I (k + 1) ω
        + (T / N) * f (gridTime T N k) (euler T N b σ S0 ΔW k ω) (Y ω) (schemeZ PN p α I k ω))
    (∀ Y₁ Y₂ : Ω → ℝ, StronglyMeasurable[𝓕 k] Y₁ → MemLp Y₁ 2 P →
        StronglyMeasurable[𝓕 k] Y₂ → MemLp Y₂ 2 P →
        ∫⁻ ω, ‖χ Y₂ ω - χ Y₁ ω‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal ((Cf * (T / N)) ^ 2) * ∫⁻ ω, ‖Y₂ ω - Y₁ ω‖ₑ ^ 2 ∂P) ∧
      (Cf * (T / N) < 1 →
        ∃ Yinf : Ω → ℝ, StronglyMeasurable[𝓕 k] Yinf ∧ MemLp Yinf 2 P ∧ Yinf =ᵐ[P] χ Yinf ∧
          ∀ Y' : Ω → ℝ, StronglyMeasurable[𝓕 k] Y' → MemLp Y' 2 P → Y' =ᵐ[P] χ Y' →
            Y' =ᵐ[P] Yinf) := by sorry

end RegMCBSDE.Projection
