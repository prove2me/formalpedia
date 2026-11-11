-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_chain_cycle_bounds
-- name    : SingleCopyMoments.Adaptive.chain_cycle_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:57.910867+00:00
-- url     : https://prove2.me/theorems/642d774a-56b4-4102-81b4-65545b3f3953
-- title:
--   Lemma 37 — All-order chain and cycle bounds
-- statement:
--   Let $K=2(\kappa+2)$ and $H(s)=1+\lfloor\log_2s\rfloor$. Under the original joint law of the physical latent prior, seed, and all $T$ outcomes, the retained ordered distinct-index chains and cycles satisfy, for $s\ge1$, $N\le T$ and $\ell\ge2$,
--
--   $$\mathbb E\|A_{s,N}\|_{HS}^2\le s^{2s}(2K^2)^s\frac{N^{H(s)}}{d^{H(s)-1}},$$
--   $$\mathbb E|C_{\ell,N}|^2\le2\ell^2(\ell-1)^{2\ell-2}(2K^2)^{\ell-1}\frac{N^{\lceil\log_2\ell\rceil+1}}{d^{\lceil\log_2\ell\rceil}}.$$
--
--   There exists one $A=A(K)\ge1$, independent of order, dimension, interpolation parameter, input seed, and strategy, with
--
--   $$\|C_{\ell,N}\|_{L^2}\le e^{A\ell\log(\ell+1)}\frac{N^{(\lceil\log_2\ell\rceil+1)/2}}{d^{\lceil\log_2\ell\rceil/2}}.$$
--
--   The joint law is a probability measure and all squared integrands are integrable. The single constant also dominates the explicit numeric square-root prefactor from the second bound, as in the proof of (7.31). None of these expectations conditions on the future event $G_\kappa$.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: one order-independent A=A(K) obtained by taking square roots of (7.30) → one existential A before all dimensions, orders, and strategies, together with its numeric prefactor domination; reason: the stated numeric predicate records the source choice of A without assuming a stochastic bound or fixing an arbitrary numeral
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 37, (7.29)–(7.31), printed p. 40 (PDF p. 42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 37, printed pp.40–42 (PDF pp.42–44), with one A=A(K) for every order. -/
theorem chain_cycle_bounds (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ A : ℝ, CycleConstant κ A ∧
      ∀ (d r : ℕ) (hd : 0 < d), 2 ≤ r → ∀ α : ℝ, 0 < α → α ≤ 1/100 →
      ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r), ∀ P : Protocol d, ∀ R : Refinement hd P,
      ∀ T N : ℕ, N ≤ T →
      let μ := jointLaw hd P r α θ T
      IsProbabilityMeasure μ ∧
      (∀ s : ℕ, 1 ≤ s →
        Integrable (fun w => hsSq (retainedChain R r α θ κ N s w)) μ ∧
        (∫ w, hsSq (retainedChain R r α θ κ N s w) ∂μ) ≤
          (s : ℝ)^(2*s) * (2*(matrixConstant κ)^2)^s *
            (N : ℝ)^chainHeight s / (d : ℝ)^(chainHeight s - 1)) ∧
      (∀ ℓ : ℕ, 2 ≤ ℓ →
        Integrable (fun w => ‖retainedCycle R r α θ κ N ℓ w‖^2) μ ∧
        (∫ w, ‖retainedCycle R r α θ κ N ℓ w‖^2 ∂μ) ≤
          2*(ℓ : ℝ)^2*((ℓ : ℝ)-1)^(2*ℓ-2) * (2*(matrixConstant κ)^2)^(ℓ-1) *
            (N : ℝ)^(level ℓ+1)/(d : ℝ)^level ℓ ∧
        Real.sqrt (∫ w, ‖retainedCycle R r α θ κ N ℓ w‖^2 ∂μ) ≤
          Real.exp (A*ℓ*Real.log ((ℓ : ℝ)+1)) *
            (N : ℝ)^(((level ℓ : ℝ)+1)/2)/(d : ℝ)^((level ℓ : ℝ)/2)) := by sorry

end SingleCopyMoments.Adaptive
