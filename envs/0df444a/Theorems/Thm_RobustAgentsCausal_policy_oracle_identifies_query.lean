-- Prove2me | Theorems.Thm_RobustAgentsCausal_policy_oracle_identifies_query
-- name    : RobustAgentsCausal.policy_oracle_identifies_query
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:33:27.030465+00:00
-- url     : https://prove2.me/theorems/f33afe92-aea1-45ef-8aa7-d40f151a5317
-- title:
--   Lemma 4: an optimal policy oracle identifies an expected-utility difference
-- statement:
--   Let the chance variables take $k_i\ge1$ values, let the decision set be finite and nonempty, and fix the decision parents $\mathrm{Pa}_D$ and the chance parents $\mathrm{Pa}_U$ of the utility. There is a procedure $F$, which uses only the utility function $U$ and a policy oracle, with the following property. For every DAG $G$ and Lebesgue-almost every parameter $(\theta_P,\theta_U)$ with $\theta_P$ valid and satisfying domain dependence (Assumption 2), let $\Pi^*_\Sigma$ be any optimal policy oracle for the mixtures of local interventions with masked inputs. Then for every masking $\mathrm{Pa}_D'\subseteq\mathrm{Pa}_D$ with $\mathrm{Pa}_D'\cap\mathrm{Pa}_U=\emptyset$, every context $\mathrm{pa}_D'$ and every mixture $\sigma$ of local interventions, $F$ returns decisions $d\ne d'$ and the number
--
--   $$\sum_{\bm z}P(\bm C=\bm c;\sigma)\,[U(d,\bm c)-U(d',\bm c)],\qquad \bm Z=\bm C\setminus\mathrm{Pa}_D'.$$
--
--   This is the basic query from which the proof of Theorem 1 recovers the conditional distributions one at a time.
--
--   **Formalization Note** "We can identify" is stated as the existence of a decoder $F$ whose inputs are the known quantities only: $U$ (with the variable domains, $\mathrm{Pa}_D$ and $\mathrm{Pa}_U$) and the oracle. $F$ is chosen before the graph and the parameters. The proof's "for almost all $P,U$" (via Lemma 3) is the almost-everywhere quantifier.
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Appendix C, Lemma 4, eq. (14) and Algorithm 1, pp. 20-21

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

theorem policy_oracle_identifies_query {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (paD paU : Finset ι) :
    ∃ F : UParam k A paU → Oracle k A → Finset ι → Cfg k → (LocalInt k → ℝ) → A × A × ℝ,
      ∀ pa : ι → Finset ι, IsAcyclic pa →
        ∀ᵐ θ : CPDParam k pa × UParam k A paU, ValidParam pa θ.1 →
          DomainDependent pa paD (utilOf paU θ.2) →
          ∀ O : Oracle k A, IsOptimalOracle paD (cpdOf pa θ.1) (utilOf paU θ.2) O →
            ∀ S ⊆ paD, Disjoint S paU → ∀ (c₀ : Cfg k) (w : LocalInt k → ℝ), IsMixture w →
              (F θ.2 O S c₀ w).1 ≠ (F θ.2 O S c₀ w).2.1 ∧
              (F θ.2 O S c₀ w).2.2 =
                ctxUtil (mixJoint (cpdOf pa θ.1) w) (utilOf paU θ.2) S c₀ (F θ.2 O S c₀ w).1 -
                  ctxUtil (mixJoint (cpdOf pa θ.1) w) (utilOf paU θ.2) S c₀ (F θ.2 O S c₀ w).2.1 := by sorry

end RobustAgentsCausal
