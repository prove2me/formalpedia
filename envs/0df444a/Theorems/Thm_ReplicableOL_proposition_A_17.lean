-- Prove2me | Theorems.Thm_ReplicableOL_proposition_A_17
-- name    : ReplicableOL.proposition_A_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:00.710289+00:00
-- url     : https://prove2.me/theorems/2fc3c2a0-96b8-4215-9d7a-0674951522ba
-- title:
--   Proposition A.17 — pointwise form
-- statement:
--   Let $\xi_j:=M_{j-1}2L\mu_j(\bar p_j-p_j)$, $\bar\xi_j:=\mathbb E[\xi_j\mid\mathcal G_{j-1}]$, $\zeta_j:=\xi_j-\bar\xi_j$ and $Q_k:=\sum_{j\le k}\mathbb E[\zeta_j^2\mid\mathcal G_{j-1}]$. Then $(\zeta_j)_{j\le k}$ is a martingale difference sequence for $(\mathcal G_j)$, $\Gamma^{\mathrm{pre}}=\sum_j\bar\xi_j+\sum_j\zeta_j$, and almost surely
--   $$
--   \sum_{j\le k}\bar\xi_j\le\sum_{j\le k}2LM_{j-1}|\mathrm{Cov}_j|\le4LC\Lambda_k,\qquad Q_k\le8L^2\Delta^2C_V\Lambda_k,\qquad|\zeta_j|\le\frac52L\Delta,
--   $$
--   where $C=C_B\Delta^2\sqrt L$ and $C_V=C_B\Delta\sqrt L$, in the regime $\Delta\sqrt L\ge\sqrt3/8$. On $\{M_k=1\}$, $\Gamma^{\mathrm{pre}}=\Gamma$.
--
--   This is the pathwise form of the proof of Theorem 2(ii),(iii), from which the tail bounds (iv) and (iv′) follow.
--
--   Differences from the source:
--   - encoding: the regime and $C$, $C_V$ fixed at the top of Section 4 (p.14) → explicit hypotheses $\sqrt3/8\le\Delta\sqrt L$, $1\le L$ and the explicit factors; reason: Section 4's standing assumptions, written into the statement
--   - encoding: $\Gamma^{\mathrm{pre}}$ and "on $\{M_k=1\}$ the two coincide" (p.15) → `∑ j, ξ j ω` and a conjunct stating equality with `gain` on $\{M_k=1\}$; reason: the definition on p.15, stated here so that it can be used
--   - generalization: the epoch rules of a learner satisfying (H2) at a fixed seed (Section 4 standing assumption, p.14) → an arbitrary `EpochRule k L`, which may read its whole current block; reason: p.17: "Within-epoch causality is not used: $\Phi_j(h;\cdot)$ may be any function of the block"; a learner's rule `𝓛.toEpochRule L r` is a special case
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Proposition A.17, p.35

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule
import Definitions.Def_ReplicableOL_hist
import Definitions.Def_ReplicableOL_M
import Definitions.Def_ReplicableOL_covJ
import Definitions.Def_ReplicableOL_Lam
import Definitions.Def_ReplicableOL_gain
import Definitions.Def_ReplicableOL_CB
import Definitions.Def_ReplicableOL_Omega4
import Definitions.Def_ReplicableOL_fourRun
import Definitions.Def_ReplicableOL_pastField
import Definitions.Def_ReplicableOL_xi
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ReplicableOL

/-- **Proposition A.17.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Proposition A.17, p.35. All clauses, with `C = C_B Δ² √L` and `C_V = C_B Δ √L` (p.14), in the regime of Section 4.

**Formalization Note.** `ξ̄_j` and `E[ζ_j² | G_{j−1}]` are Mathlib `condExp`. The martingale-difference property is `pastField (j + 1)`-measurability plus a vanishing conditional mean. The last conjuncts record `Γ^pre = Σ ξ_j` and, from p.15, `Γ^pre = Γ` on `{M_k = 1}`. -/
theorem proposition_A_17 {k L : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 4) (hL : 1 ≤ L)
    (hreg : √3 / 8 ≤ Δ * √(L : ℝ)) (Φ : EpochRule k L) :
    let ξ : Fin k → Omega4 k L → ℝ := fun j ω => xi Δ Φ j ω.1 ω.2.1 ω.2.2.1
    let ξbar : Fin k → Omega4 k L → ℝ := fun j => (fourRun Δ k L)[ξ j | pastField j.val]
    let ζ : Fin k → Omega4 k L → ℝ := fun j ω => ξ j ω - ξbar j ω
    let Q : Omega4 k L → ℝ := fun ω => ∑ j : Fin k,
      ((fourRun Δ k L)[fun ω' => ζ j ω' ^ 2 | pastField j.val]) ω
    (∀ j : Fin k, Measurable[pastField (j.val + 1)] (ζ j) ∧
      (fourRun Δ k L)[ζ j | pastField j.val] =ᵐ[fourRun Δ k L] 0) ∧
    (∀ ω, ∑ j : Fin k, ξ j ω = ∑ j : Fin k, ξbar j ω + ∑ j : Fin k, ζ j ω) ∧
    (∀ ω : Omega4 k L, M Φ k ω.2.1 ω.2.2.1 = 1 → ∑ j : Fin k, ξ j ω = gain Δ Φ ω.1 ω.2.1) ∧
    (∀ᵐ ω ∂(fourRun Δ k L),
      ∑ j : Fin k, ξbar j ω ≤
        ∑ j : Fin k, 2 * (L : ℝ) * M Φ j.val ω.2.1 ω.2.2.1 * |covJ Δ Φ j (hist ω.2.1 j)|) ∧
    (∀ᵐ ω ∂(fourRun Δ k L),
      ∑ j : Fin k, 2 * (L : ℝ) * M Φ j.val ω.2.1 ω.2.2.1 * |covJ Δ Φ j (hist ω.2.1 j)| ≤
        4 * (L : ℝ) * (CB * Δ ^ 2 * √(L : ℝ)) * Lam Δ Φ ω.2.1 ω.2.2.1) ∧
    (∀ᵐ ω ∂(fourRun Δ k L),
      Q ω ≤ 8 * (L : ℝ) ^ 2 * Δ ^ 2 * (CB * Δ * √(L : ℝ)) * Lam Δ Φ ω.2.1 ω.2.2.1) ∧
    (∀ᵐ ω ∂(fourRun Δ k L), ∀ j : Fin k, |ζ j ω| ≤ 5 / 2 * (L : ℝ) * Δ) := by sorry

end ReplicableOL
