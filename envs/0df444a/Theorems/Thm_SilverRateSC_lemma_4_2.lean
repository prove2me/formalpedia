-- Prove2me | Theorems.Thm_SilverRateSC_lemma_4_2
-- name    : SilverRateSC.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:47:54.903206+00:00
-- url     : https://prove2.me/theorems/a6ce3e51-1f9a-413b-892e-44288753e9b2
-- title:
--   Lemma 4.2 — bounds for repair checkpoints
-- statement:
--   Fix $C_0\ge1$. There are constants $\xi_0\in(0,1)$ and $c_0>0$, depending only on $C_0$, with the following property. Let $\kappa\ge4$, $1\le S_0\le\xi_0\kappa/C_0$, and let $h_1,\dots,h_r\ge0$ be the stepsizes of the unselected tail with $S_0\le S:=\sum_th_t\le C_0S_0$. For any checkpoints $t_1<\dots<t_q$ selected by the repair rule of §4.2 and every incoming pair $\ell_1\ge0$, $D_1>0$ with $\ell_1/D_1\le32C_0$, the Huber repair components of Lemma 3.2 can be constructed successively at these checkpoints: they satisfy $\eta_i>0$ and $D_{i+1}>0$ for every $1\le i\le q$, and
--   1. $D_{q+1}/D_1\ge c_0(r+1)^{-4}$;
--   2. $\ell_{q+1}/D_{q+1}\le32C_0$;
--   3. $\sum_{t=t_q+1}^rh_t\le S_0/4$.
--
--   Repairs therefore lose at most a polynomial factor in the number of steps they consider, keep the relative threshold bounded, and leave a short tail.
--
--   Differences from the source:
--   - encoding: the Huber repair components of Lemma 3.2 constructed successively at the checkpoints, giving pairs (ℓ_{i+1}, D_{i+1}) → repairChain: (ℓ_{i+1}, D_{i+1}) computed from (ℓ_i, D_i) by the closed forms (13)–(14) on the i-th gap with checkpoint stepsize h_{t_i}; η_i > 0 asserted for each i; reason: Lemma 3.2 shows the repair trajectory has exactly these outgoing pairs once η_i > 0 (the gap steps are < κ since S ≤ C_0S_0 ≤ ξ_0κ < κ)
--   - encoding: checkpoints selected by the rule; t_0 = 0; (r+1)^{−4} → ts with IsRepairSelection S₀ r h ts, t_i = ckpt ts i; integer power ((r:ℝ)+1)^(−4); reason: same selections and value
--   - encoding: tail stepsizes h_1, …, h_r ≥ 0, S = h_1 + ⋯ + h_r, q → h : ℕ → ℝ read at positions 1, …, r, S = ∑ t ∈ Finset.Icc 1 r, h t, q = ts.length; reason: same data; entries outside 1, …, r are unconstrained and unused
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 4.2, p.18; rule §4.2, p.18; components (13)–(14), pp.15–16

import Mathlib
import Definitions.Def_SilverRateSC_IsRepairSelection
import Definitions.Def_SilverRateSC_repairChain

namespace SilverRateSC

/-- **Lemma 4.2 (Bounds for repair checkpoints).** Fix `C_0 ≥ 1`. There are constants
`ξ_0 ∈ (0, 1)` and `c_0 > 0`, depending only on `C_0`, with the following property. Let `κ ≥ 4`,
`1 ≤ S_0 ≤ ξ_0 κ/C_0`, and `S_0 ≤ S ≤ C_0 S_0`. For any checkpoints selected by the repair rule and
every incoming pair `ℓ_1 ≥ 0`, `D_1 > 0` with `ℓ_1/D_1 ≤ 32C_0`, the Huber repair components of
Lemma 3.2 can be constructed successively at these checkpoints. They satisfy `η_i > 0` and
`D_{i+1} > 0` for every `1 ≤ i ≤ q`, with (i) `D_{q+1}/D_1 ≥ c_0(r + 1)^{−4}`,
(ii) `ℓ_{q+1}/D_{q+1} ≤ 32C_0`, (iii) `∑_{t=t_q+1}^r h_t ≤ S_0/4`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 4.2, p. 18 (rule §4.2, p. 18; components (13)–(14), pp. 15–16).

**Formalization Note** `h_1, …, h_r ≥ 0` are the tail stepsizes (`h : ℕ → ℝ` at positions
`1, …, r`) and `S = ∑ h_t`. "Selected by the rule" is `IsRepairSelection S₀ r h ts`, `q = ts.length`,
`t_i = ckpt ts i`, `t_0 = 0`. "Constructed successively" is `repairChain`: `(ℓ_{i+1}, D_{i+1})` is
`repairChain … i`, obtained from `(ℓ_i, D_i)` by the closed forms (13)–(14) of the Huber repair on the
`i`-th gap `gapList h ts i` with checkpoint stepsize `h_{t_i}`; `η_i` is `etaGap` on that gap with
`(ℓ_i, D_i)`. `(r + 1)^{−4}` is an integer power. -/
theorem lemma_4_2 (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ ξ₀ c₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 ∧ 0 < c₀ ∧
      ∀ κ S₀ : ℝ, 4 ≤ κ → 1 ≤ S₀ → S₀ ≤ ξ₀ * κ / C₀ →
      ∀ (r : ℕ) (h : ℕ → ℝ), (∀ t ∈ Finset.Icc 1 r, 0 ≤ h t) →
        S₀ ≤ ∑ t ∈ Finset.Icc 1 r, h t → ∑ t ∈ Finset.Icc 1 r, h t ≤ C₀ * S₀ →
      ∀ ts : List ℕ, IsRepairSelection S₀ r h ts →
      ∀ ℓ₁ D₁ : ℝ, 0 ≤ ℓ₁ → 0 < D₁ → ℓ₁ / D₁ ≤ 32 * C₀ →
        (∀ i ∈ Finset.Icc 1 ts.length,
          0 < etaGap κ (gapList h ts i) (repairChain κ h ts ℓ₁ D₁ (i - 1)).1
            (repairChain κ h ts ℓ₁ D₁ (i - 1)).2 ∧
          0 < (repairChain κ h ts ℓ₁ D₁ i).2) ∧
        c₀ * ((r : ℝ) + 1) ^ (-4 : ℤ) ≤ (repairChain κ h ts ℓ₁ D₁ ts.length).2 / D₁ ∧
        (repairChain κ h ts ℓ₁ D₁ ts.length).1 / (repairChain κ h ts ℓ₁ D₁ ts.length).2 ≤
          32 * C₀ ∧
        ∑ t ∈ Finset.Icc (ckpt ts ts.length + 1) r, h t ≤ S₀ / 4 := by sorry

end SilverRateSC
