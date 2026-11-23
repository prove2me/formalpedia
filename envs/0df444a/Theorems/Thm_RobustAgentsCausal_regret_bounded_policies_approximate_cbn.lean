-- Prove2me | Theorems.Thm_RobustAgentsCausal_regret_bounded_policies_approximate_cbn
-- name    : RobustAgentsCausal.regret_bounded_policies_approximate_cbn
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:34:46.462488+00:00
-- url     : https://prove2.me/theorems/8ca03701-a2e8-4273-98d0-17417a0f67df
-- title:
--   Theorem 2 (as proved): regret-bounded policies identify the parameters of $\mathrm{Anc}_U$ up to $O(\delta)$
-- statement:
--   Let the chance variables take $k_i\ge1$ values, let the decision set be finite and nonempty, and fix $\mathrm{Pa}_D$ and $\mathrm{Pa}_U$. There is a procedure $F$, which uses only the regret bound $\delta$, the utility function $U$ and a policy oracle, with the following property. For every DAG $G$ and Lebesgue-almost every parameter $(\theta_P,\theta_U)$ with $\theta_P$ valid and satisfying Assumption 2, there are constants $C$ and $\delta_0>0$ such that the following holds for every $0\le\delta\le\delta_0$. If $\Pi^\delta_\Sigma$ is a policy oracle whose policies satisfy
--
--   $$\mathbb E^{\pi_\sigma}[U]\ge\mathbb E^{\pi^*_\sigma}[U]-\delta$$
--
--   for every mixture $\sigma$ of local interventions and every masking, then the conditional distributions $P'(c_i\mid\mathrm{pa}_i)$ returned by $F(\delta,U,\Pi^\delta_\Sigma)$ satisfy, for every $C_i\in\mathrm{Anc}_U$ and every $c_i$, $\mathrm{pa}_i$,
--
--   $$\big|P'(c_i\mid\mathrm{pa}_i)-P(c_i\mid\mathrm{pa}_i)\big|\le\gamma(\delta):=C\delta.$$
--
--   So $\gamma(0)=0$ and $\gamma$ grows linearly in $\delta$ for small regret.
--
--   **Formalization Note** The paper claims the bound for all variables $V_i\in\bm V$. That is false for chance variables outside $\mathrm{Anc}_U$, whose conditional distributions do not affect any expected utility and so cannot be recovered even when $\delta=0$. Its proof treats exactly the variables of $\mathrm{Anc}_U$, as in Theorem 1. "Grows linearly in $\delta$ for small regret $\delta\ll\mathbb E^{\pi^*}[U]$" is read as $\gamma(\delta)\le C\delta$ on some interval $[0,\delta_0]$, with $C$ and $\delta_0$ depending on the CID. Conditional distributions are compared at every joint state; the approximate graph $G'$, about which the theorem asserts nothing further, is not part of the statement.
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Section 3.1, Theorem 2, p. 5; proof in Appendix D, pp. 24-28

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

theorem regret_bounded_policies_approximate_cbn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (hk : ∀ i, 0 < k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (paD paU : Finset ι) :
    ∃ F : ℝ → UParam k A paU → Oracle k A → (i : ι) → Cfg k → Fin (k i) → ℝ,
      ∀ pa : ι → Finset ι, IsAcyclic pa →
        ∀ᵐ θ : CPDParam k pa × UParam k A paU, ValidParam pa θ.1 →
          DomainDependent pa paD (utilOf paU θ.2) →
          ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₀ →
            ∀ O : Oracle k A, IsDeltaOptimalOracle δ paD (cpdOf pa θ.1) (utilOf paU θ.2) O →
              ∀ i ∈ ancU pa paD paU, ∀ (c : Cfg k) (v : Fin (k i)),
                |F δ θ.2 O i c v - cpdOf pa θ.1 i c v| ≤ C * δ := by sorry

end RobustAgentsCausal
