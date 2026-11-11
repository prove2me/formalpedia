-- Prove2me | Theorems.Thm_QIndInf_recovery_step_bound
-- name    : QIndInf.recovery_step_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:16.437904+00:00
-- url     : https://prove2.me/theorems/86f0fc90-d0f5-4b7b-aaba-4c26ac40062e
-- title:
--   Eqs. (66)–(68) — per-round recovery bound
-- statement:
--   Let $\tau$ and $\mu$ be density operators on a bipartite system $A\otimes B$ with $\mathrm{supp}(\tau)\subseteq\mathrm{supp}(\mu)$, let $\mathcal N=\mathrm{Tr}_B$, and let
--
--   $$
--   \mathcal R_{\mu,\mathcal N}(\cdot)=\frac\pi2\int_{\mathbb R}dt\,(\cosh(\pi t)+1)^{-1}\,\mathcal R^{t/2}_{\mu,\mathcal N}(\cdot)
--   $$
--
--   be the averaged rotated Petz recovery map (Eq. (26)). Then
--
--   $$
--   D(\tau\|\mu)-D\big(\mathcal N(\tau)\,\big\|\,\mathcal N(\mu)\big)\ \ge\ \mathrm{TD}\big(\mathcal R_{\mu,\mathcal N}(\mathcal N(\tau)),\,\tau\big)^2 .
--   $$
--
--   In the proof of Theorem 4.2 this is applied with $A=R_1\cdots R_{i-1}$, $B=R_iX_i$, $\tau=\tau_{\le i|h<i}$, $\mu=\mu_{\le i|h<i}$, where $\mathcal N(\tau)=\rho_{<i|h<i}$ (Eq. (65)) and $\mathcal R_{\mu,\mathcal N}(\rho_{<i|h<i})$ is the learner's output: it bounds the learner's squared error in one round by the growth of relative entropy. The paper derives it from Lemma 3.3, the Fuchs–van de Graaf inequality and $1-F^2\le-2\ln F$.
--
--   **Formalization Note** $D$ is the published `relativeEntropy` in nats, $\mathrm{TD}=\tfrac12$`WildeQIT.traceDist`, and $\mathcal R$ is the published `recovery` (exactly Eq. (26); its entries are integrals of bounded continuous functions against a probability density).
--
--   Differences from the source:
--   - generalization: τ = τ_{≤i|h<i}, μ = μ_{≤i|h<i}, N = N_i = Tr_{R_iX_i} → any density operators τ, μ on A × B with supp τ ⊆ supp μ, N = Tr_B; reason: the paper's pair is an instance (support inclusion from Eq. (58)), and N_i(τ) = ρ_{<i|h<i} by Eq. (65)
--   - generalization: D in bits (p.14) on the left of (68) → D in nats; reason: the left side is nonnegative (data processing), and D in bits = D in nats / ln 2 ≥ D in nats, so the nats inequality implies the bits inequality
--   - encoding: TD(L(param, h<i, I_i, ρ_{<i|h<i}), τ_{≤i|h<i}) with L = R_{μ,N_i} (Eq. (67), step 4) → TD(R_{μ,N}(N(τ)), τ) = ½ traceDist; reason: the learner's output is R_{μ_{≤i|h<i},N_i}(ρ_{<i|h<i}) by step 4 of the algorithm; TD = ½‖·‖₁
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eqs. (66)–(68), p.21; recovery map: Lemma 3.3, Eq. (26), p.15

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21

set_option autoImplicit false

namespace QIndInf

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy recovery)

/-- **Per-round recovery bound** (Eqs. (66)–(68)). Let `τ` and `μ` be density operators on a
bipartite system `A ⊗ B` with `supp τ ⊆ supp μ`, let `N = Tr_B`, and let `R_{μ,N}` be the averaged
rotated Petz recovery map of Eq. (26). Then
`D(τ‖μ) − D(N(τ)‖N(μ)) ≥ TD(R_{μ,N}(N(τ)), τ)²`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.2, Eqs. (66)–(68), p.21, applied there with
`A = (R₁ … R_{i−1})`, `B = (R_i, X_i)`, `τ = τ_{≤i|h<i}`, `μ = μ_{≤i|h<i}`, `N = N_i` and
`N(τ) = ρ_{<i|h<i}`, `N(μ) = μ_{<i|h<i}` (Eq. (65)); the recovery map is that of Lemma 3.3,
Eq. (26), p.15.

**Formalization Note.**
* `TD = ½ · WildeQIT.traceDist`.
* `R_{μ,N}` is the published `P21.recovery μ N` (`∫ β₀(t) R^{t/2}_{μ,N} dt`,
  `β₀(t) = π / (2 (cosh πt + 1))`, exactly Eq. (26)); its entries are integrals of bounded
  continuous functions against a probability density, so no Bochner default value arises.
* `D` is the published `P21.relativeEntropy` in nats. The paper's `D` is in bits (p.14); since the
  left side is nonnegative (data processing), the bits form follows from this one by dividing by
  `ln 2 < 1`.
* `supp τ ⊆ supp μ` is `P21.IsSupported τ μ` (kernel inclusion). -/
theorem recovery_step_bound {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (τ μ : Matrix (A × B) (A × B) ℂ) (hτ : WildeQIT.IsDensityOperator τ)
    (hμ : WildeQIT.IsDensityOperator μ) (hsupp : IsSupported τ μ) :
    ((((1 / 2 : ℝ) * WildeQIT.traceDist
        (recovery μ WildeQIT.partialTraceRight (WildeQIT.partialTraceRight τ)) τ) ^ 2 : ℝ) : EReal) ≤
      relativeEntropy τ μ -
        relativeEntropy (WildeQIT.partialTraceRight τ) (WildeQIT.partialTraceRight μ) := by sorry

end QIndInf
