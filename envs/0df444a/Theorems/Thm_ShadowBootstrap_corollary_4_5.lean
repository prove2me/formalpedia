-- Prove2me | Theorems.Thm_ShadowBootstrap_corollary_4_5
-- name    : ShadowBootstrap.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:17.818952+00:00
-- url     : https://prove2.me/theorems/82da6f1f-36cf-40a1-85cd-400911e66a23
-- title:
--   Corollary 4.5 — $J = \lceil\log_2(1/(2\epsilon))\rceil$ stages give $\mathbb E[1-\mathrm{Tr}(\psi\sigma_J)] \le \epsilon$ with $O(\log(1/\epsilon))$ bases and $O(d/\epsilon)$ copies
-- statement:
--   Let $E$ be a Clifford ensemble with invertible shadow channel satisfying Eq. (8) with constant $C_F$, and $C = C_F + 1$. Fix unit vectors $|\psi\rangle, |\sigma_0\rangle$ with $\operatorname{Tr}(\psi\sigma_0) \ge 1/2$. For $\epsilon \in (0,1)$ let $J := \lceil\log_2(1/(2\epsilon))\rceil$ (no stage when this is $\le 0$), and run the stages $t = 1, \dots, J$ with
--   $$N_t := \lceil 16(C+1)\rceil,\qquad S_t := d\,2^{t-1},$$
--   each stage using fresh independent bases from $E$ and fresh copies. Then
--   $$\mathbb E\big[1 - \operatorname{Tr}(\psi\sigma_J)\big] \le \epsilon,\qquad \sum_{t=1}^J N_t \le K\log(1/\epsilon),\qquad \sum_{t=1}^J N_tS_t \le K\,\frac d\epsilon,$$
--   where $K$ depends only on $C_F$. In particular there exist choices of $N_t, S_t$ with $\sum_t N_t = O(\log(1/\epsilon))$ and $\sum_t N_tS_t = O(d/\epsilon)$, as printed.
--
--   This is the refinement guarantee: from constant overlap, $O(\log(1/\epsilon))$ fresh bases suffice for expected infidelity $\epsilon$.
--
--   Differences from the source:
--   - generalization: there exist choices of N_t, S_t → the proof's choices N_t = ⌈16(C+1)⌉ with C = C_F + 1 and S_t = d2^{t−1}; reason: the bound for specific choices implies the existence statement
--   - reading: a Clifford ensemble satisfying Lemma 3.8 (Eq. (8)) → any finite ensemble whose positive-weight unitaries are Clifford, with invertible shadow channel, satisfying Var[Tr(Oρ̂)] ≤ C_F‖O‖_F² for every state and Hermitian O; reason: this is Definition 4.1's hypothesis; invertibility is presupposed by M⁻¹
--   - encoding: J := ⌈log₂(1/(2ϵ))⌉ → the integer part toNat of the ceiling (0 stages when ϵ ≥ 1/2); reason: J counts stages; a nonpositive ceiling means no stage
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Corollary 4.5 and its proof, p.15

import Mathlib
import Definitions.Def_ShadowBootstrap_stagesExpect
import Definitions.Def_ShallowShadows_ShadowNorm_IsCliffordPrimitive

open ClassicalShadow.Linear ShallowShadows.ShadowNorm

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Corollary 4.5, p.15: fix an initial estimate `σ₀` with `Tr(ψσ₀) ≥ 1/2`. For any `ϵ ∈ (0, 1)`, let
`J := ⌈log₂(1/(2ϵ))⌉`. There exist choices of `N_t, S_t` for `t = 1, …, J` such that
`E[1 − Tr(ψσ_J)] ≤ ϵ` and `Σ_t N_t = O(log(1/ϵ))`, `Σ_t N_t S_t = O(d/ϵ)`.

**Formalization Note** The choices are the proof's, `N_t := ⌈16(C + 1)⌉` and `S_t := d 2^{t−1}`,
with `C = C_F + 1` the constant of Lemma 4.2 for an ensemble satisfying Eq. (8) with `C_F`; stated
for these choices, the theorem implies the printed "there exist choices". The `O(·)` constant `K`
depends on `C_F` only. `J` is `0` when `⌈log₂(1/(2ϵ))⌉ ≤ 0` (`ϵ ≥ 1/2`). The stages use independent
bases and disjoint copies; `stagesExpect` is the expectation over all stages' data, and `σ_J`
results from Eqs. (12)–(13) with the fixed vector `σ₀`. -/
theorem corollary_4_5 :
    ∀ CF : ℝ, ∃ K : ℝ, ∀ (n : ℕ) {ι : Type} [Fintype ι] (E : Primitive n ι),
      IsCliffordPrimitive E → IsUnit (measChannel E) →
      (∀ ρ : Op n, WildeQIT.IsDensityOperator ρ → ∀ O : Op n, O.IsHermitian →
        snapVar E ρ O ≤ CF * frobSq O) →
      ∀ ψ σ₀ : Bits n → ℂ, IsUnitVec ψ → IsUnitVec σ₀ → 1 / 2 ≤ ‖braket ψ σ₀‖ ^ 2 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        stagesExpect E ψ σ₀
            ((List.range (⌈Real.logb 2 (1 / (2 * ε))⌉).toNat).map
              fun t => (⌈16 * (CF + 2)⌉₊, 2 ^ n * 2 ^ t))
            σ₀ (fun σ => 1 - ‖braket ψ σ‖ ^ 2) ≤ ε ∧
        ((((List.range (⌈Real.logb 2 (1 / (2 * ε))⌉).toNat).map
              fun _ => ⌈16 * (CF + 2)⌉₊).sum : ℕ) : ℝ) ≤ K * Real.log (1 / ε) ∧
        ((((List.range (⌈Real.logb 2 (1 / (2 * ε))⌉).toNat).map
              fun t => ⌈16 * (CF + 2)⌉₊ * (2 ^ n * 2 ^ t)).sum : ℕ) : ℝ) ≤ K * 2 ^ n / ε := by sorry

end ShadowBootstrap
