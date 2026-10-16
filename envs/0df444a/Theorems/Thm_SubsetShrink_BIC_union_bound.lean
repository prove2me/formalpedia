-- Prove2me | Theorems.Thm_SubsetShrink_BIC_union_bound
-- name    : SubsetShrink.BIC.union_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:34.116748+00:00
-- url     : https://prove2.me/theorems/432851fb-4300-48ee-b2dd-fe0e247b18f1
-- title:
--   p. 50 — union bound over model sizes: P(Gᶜ) ≤ ϵ0 for G = ∩_s G_s at δ0 = (s/[ep])^s ϵ0 (corrected G_s)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ ($p\ge 1$) have unit-norm columns, $\epsilon\sim N(0,\sigma^2I_n)$ with $\sigma>0$, and $\epsilon_0\in(0,1)$. For $s=1,\dots,p$ put $\delta_s=(s/[ep])^s\epsilon_0$ and consider the event $G'_s$ (see the definition file) at $\delta_0=\delta_s$. Let $G=\bigcap_{s=1}^pG'_s$. Then $G$ is measurable and
--   $$P(G^c)\le\sum_{s=1}^pP(G_s'^{\,c})\le\sum_{s=1}^p(s/[ep])^s\epsilon_0\le\sum_{s=1}^pe^{-s}\epsilon_0\le\epsilon_0,$$
--   so that $P(G)\ge1-\epsilon_0$.
--
--   The event $G$ controls $\epsilon^\top Xu$ simultaneously over all sparsity levels, which is what lets the penalty $\mu_\beta\|\beta\|_0$ select the model size.
--
--   **Formalization Note** The page uses the event $G_s$ of §3.1, whose printed probability bound is false (see the definition file); the statement uses the corrected $G'_s$, with $3\log(1/\delta_0)$ in place of $\log(1/\delta_0)$. Each link of the printed chain is a separate conjunct; the second link is the corrected $G_s$ part of Theorem 1 at $\delta_0=\delta_s\in(0,1)$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 50, proof of Theorem 5 (B.13), definition of G and the display P(Gᶜ) ≤ … ≤ ϵ0; event G_s of p. 13 (corrected)

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- p. 50: with `δ_s = (s/[ep])^s ϵ0` and `G = ⋂_{s=1}^p G'_s` (corrected events, `G'_s` taken at
`δ0 = δ_s`), `P(Gᶜ) ≤ ∑_s P(G'_sᶜ) ≤ ∑_s δ_s ≤ ∑_s e^{−s} ϵ0 ≤ ϵ0`, hence `P(G) ≥ 1 − ϵ0`. -/
theorem union_bound {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ ϵ0 : ℝ)
    (hX : SubsetShrink.Events.UnitCols X) (hp : 1 ≤ p) (hσ : 0 < σ) (hϵ0 : 0 < ϵ0) (hϵ1 : ϵ0 < 1) :
    MeasurableSet (⋂ s ∈ Finset.Icc 1 p,
        SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s) ∧
    (SubsetShrink.Events.noiseLaw n σ (⋂ s ∈ Finset.Icc 1 p,
        SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)ᶜ).toReal ≤
      ∑ s ∈ Finset.Icc 1 p,
        (SubsetShrink.Events.noiseLaw n σ (SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)ᶜ).toReal ∧
    (∀ s ∈ Finset.Icc 1 p,
      (SubsetShrink.Events.noiseLaw n σ (SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)ᶜ).toReal ≤
        ((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) ∧
    ∑ s ∈ Finset.Icc 1 p, ((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0 ≤
      ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) * ϵ0 ∧
    ∑ s ∈ Finset.Icc 1 p, Real.exp (-(s : ℝ)) * ϵ0 ≤ ϵ0 ∧
    1 - ϵ0 ≤ (SubsetShrink.Events.noiseLaw n σ (⋂ s ∈ Finset.Icc 1 p,
        SubsetShrink.Events.Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)).toReal := by sorry

end SubsetShrink.BIC
