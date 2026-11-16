-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_Supplement_cor_23
-- name    : TFIMPhaseDiagram.Classical.Supplement.cor_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:56.236052+00:00
-- url     : https://prove2.me/theorems/0a240bbf-039c-4f95-b3ee-3b5988c0f73b
-- title:
--   Corollary 23 — Uniform conditioned gadget partition estimates
-- statement:
--   Fix $b,\eta>0$ with $(b/\eta)\tanh\eta>1$, let $m_\ast\in(0,1)$ be the positive magnetization, and fix $t\ge1$ and $0<\delta<m_\ast$. There is an integer $r_0>0$, depending only on $b,\eta,t,\delta$, such that for every $r\ge r_0$, every family of measurable spin boundary paths $\tau_1,\ldots,\tau_t$ and both signs $s\in\{-1,1\}$,
--   $$
--   Q_s(\tau)=e^{\pm3bt\delta} A_0\exp\!\left(bs m_\ast\sum_{j=1}^t\langle\tau_j,1\rangle\right).
--   $$
--   Here $Q_s$ and $A_0$ are exactly the integrals in (20), with $r$ free spins, and the gadget phase is positive precisely when its average is strictly closer to $m_\ast1$; ties have negative phase. The estimate is uniform over the boundary paths and is the conditioned partition estimate used in the hardness construction. The threshold is the integer ceiling of the explicit p.19 formula, using the least concentration threshold enlarged as on p.18.
--
--   Differences from the source:
--   - encoding: S={1,...,t} and R={t+1,...,n}, with r=n-t → disjoint Fin t and Fin r blocks, so n=t+r; reason: canonical finite reindexing preserves every n>t≥1 instance
--   - encoding: measurable spin-valued paths and signed real multiplicative accuracy → their L² classes, Bool-coded signs, and the published complex ExpApprox on real casts; reason: null modifications do not affect the integrals, and real casts preserve the exact multiplicative relation
--   - encoding: the existential threshold r0 and its explicit formula on pp.18–19 → gadgetThreshold, with the least enlarged concentration threshold and integer ceiling; reason: the source proof supplies this parameter-only witness; the ceiling plus one ensures a positive integer threshold
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026); pinned source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, pp. 15, Corollary 23

import Definitions.Def_TFIMPhaseDiagram_Classical_Supplement_deviations

set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators ENNReal
noncomputable section

namespace TFIMPhaseDiagram.Classical.Supplement
attribute [local instance] Classical.propDecidable

/-- Corollary 23, p.15; r=n-t, reindexed as disjoint Fin t and Fin r blocks. -/
theorem cor_23 (b η : ℝ) (h : supercritical b η) (t : ℕ) (ht : 0 < t)
    (δ : ℝ) (hd : 0 < δ) (hdm : δ < magnetization b η) :
    IsConcentrationThreshold b η δ (concentrationThreshold b η δ) ∧
    ∃ r₀ : ℕ, r₀ = gadgetThreshold b η δ t ∧ 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∀ τ : Fin t → CircleL2, (∀ j, IsSpinClass (τ j)) → ∀ s : Bool,
        ExpApprox (3*b*t*δ) (gadgetQ b η (magnetization b η) r τ s)
          (gadgetA b η (magnetization b η) δ r *
            Real.exp (b * phaseSign s * magnetization b η * ∑ j, circleMean (τ j))) := by sorry

end TFIMPhaseDiagram.Classical.Supplement
