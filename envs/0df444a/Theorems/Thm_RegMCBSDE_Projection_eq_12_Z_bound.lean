-- Prove2me | Theorems.Thm_RegMCBSDE_Projection_eq_12_Z_bound
-- name    : RegMCBSDE.Projection.eq_12_Z_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:31.536148+00:00
-- url     : https://prove2.me/theorems/21c5d217-9146-4e4c-9daa-19c071ad25de
-- title:
--   Proof of Theorem 2, Step 1, Eq. (12) — h E|Z^{N,i,I}_{l,t_k}|² ≤ E[Y^{N,I,I}_{t_{k+1}}]² − E[E_k(Y^{N,I,I}_{t_{k+1}})]²
-- statement:
--   Assume (H1)–(H2) and the standing model, let the bases have invertible Gram matrices, and let $\alpha$ be a projection–Picard scheme with $I$ iterations. Write $h=T/N$ and $\mathbb E_k=\mathbb E(\cdot\mid\mathcal F_k)$. For every $i\ge1$, every $0\le k\le N-1$ and every $1\le l\le q$:
--
--   1. $Z^{N,i,I}_{t_k}=Z^{N,1,I}_{t_k}$ almost surely, i.e. $Z^{N,i,I}_{t_k}$ does not depend on $i\ge1$;
--   2. the following bound holds:
--   $$h\,\mathbb E|Z^{N,i,I}_{l,t_k}|^2+\mathbb E\big|\mathbb E_k\big(Y^{N,I,I}_{t_{k+1}}\big)\big|^2\le\mathbb E\big|Y^{N,I,I}_{t_{k+1}}\big|^2 .$$
--
--   The second item is the paper's (12), $\mathbb E|Z^{N,i,I}_{l,t_k}|^2\le\frac1h\big(\mathbb E[Y^{N,I,I}_{t_{k+1}}]^2-\mathbb E[\mathbb E_k(Y^{N,I,I}_{t_{k+1}})]^2\big)$. The conditional-variance term on the right is what keeps the later estimates from exploding as $h\to0$.
--
--   **Formalization Note** (12) is multiplied by $h$ and rearranged so that no subtraction occurs; expectations are taken in $[0,\infty]$. The paper's $\mathbb E[X]^2$ means $\mathbb E[X^2]$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 12, Proof of Theorem 2, Step 1, Eq. (12)

import Mathlib
import Definitions.Def_RegMCBSDE_Projection_Scheme

namespace RegMCBSDE.Projection

open MeasureTheory ProbabilityTheory

/-- **Proof of Theorem 2, Step 1, Eq. (12)** (arXiv:math/0508491v1, p. 12). For every `i ≥ 1`,
`k < N` and component `m : Fin q` (the paper's `l = m + 1`), with `h = T/N`:

* `Z^{N,i,I}_{t_k}` does not depend on `i ≥ 1`: it equals `Z^{N,1,I}_{t_k}` almost surely;
* `h 𝔼|Z^{N,i,I}_{l,t_k}|^2 + 𝔼|𝔼_k(Y^{N,I,I}_{t_{k+1}})|^2 ≤ 𝔼|Y^{N,I,I}_{t_{k+1}}|^2`.

The second item is (12), `𝔼|Z^{N,i,I}_{l,t_k}|^2 ≤ h⁻¹(𝔼[Y^{N,I,I}_{t_{k+1}}]^2 - 𝔼[𝔼_k(Y^{N,I,I}_{t_{k+1}})]^2)`,
multiplied by `h` and rearranged so that no subtraction occurs in `[0, ∞]`. -/
theorem eq_12_Z_bound (T : ℝ) (hT : 0 < T) {d q d' : ℕ}
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
    (i : ℕ) (hi : 1 ≤ i) (k : ℕ) (hk : k < N) (m : Fin q) :
    schemeZ PN p α i k =ᵐ[P] schemeZ PN p α 1 k ∧
      ENNReal.ofReal (T / N) * ∫⁻ ω, ‖schemeZ PN p α i k ω m‖ₑ ^ 2 ∂P
          + ∫⁻ ω, ‖(P[schemeY N PN ΦN p α I (k + 1) | 𝓕 k]) ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, ‖schemeY N PN ΦN p α I (k + 1) ω‖ₑ ^ 2 ∂P := by sorry

end RegMCBSDE.Projection
