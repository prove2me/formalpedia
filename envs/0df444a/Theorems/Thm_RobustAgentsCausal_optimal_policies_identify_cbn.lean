-- Prove2me | Theorems.Thm_RobustAgentsCausal_optimal_policies_identify_cbn
-- name    : RobustAgentsCausal.optimal_policies_identify_cbn
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:34:09.380283+00:00
-- url     : https://prove2.me/theorems/45732da5-0c91-4856-8e45-6abd0dab550f
-- title:
--   Theorem 1: optimal policies under domain shifts identify the causal Bayesian network
-- statement:
--   Let the chance variables $C_i$ take $k_i\ge2$ values, let the decision set be finite and nonempty, and fix the decision parents $\mathrm{Pa}_D$ and the chance parents $\mathrm{Pa}_U$ of the utility. There is a procedure $F$, which uses only the utility function $U$ and a policy oracle, with the following property. For every DAG $G$ on the chance variables and Lebesgue-almost every parameter $(\theta_P,\theta_U)$ of the CID $M=(G,P)$ with $\theta_P$ valid, satisfying Assumption 2, let
--
--   $$\Pi^*_\Sigma:\sigma\mapsto\pi^*_\sigma(d\mid\mathrm{pa}_D)$$
--
--   be any optimal policy oracle on the set $\Sigma$ of mixtures of local interventions with masked inputs. Then $F(U,\Pi^*_\Sigma)$ returns:
--
--   1. the set of chance variables in $\mathrm{Anc}_U$;
--   2. the parent set $\mathrm{Pa}_i$ in $G$ of every $C_i\in\mathrm{Anc}_U$;
--   3. the conditional distribution $P(c_i\mid\mathrm{pa}_i)$ of every $C_i\in\mathrm{Anc}_U$.
--
--   That is, the oracle determines the graph $G(\mathrm{Anc}_U)$ and the joint distribution $P(\mathrm{Anc}_U)$.
--
--   In words, an agent that acts optimally under every mixture of local domain shifts carries enough information to reconstruct the causal Bayesian network of every variable relevant to its utility.
--
--   **Formalization Note** "We can identify" is stated as the existence of a decoder $F$ chosen before the graph and the parameters. Its inputs are the known data: the variables and their domains, $\mathrm{Pa}_D$, $\mathrm{Pa}_U$ and $U$. It must work for every optimal oracle, since optimal policies are not unique at ties. The hypothesis $k_i\ge2$ is not in the paper. Without it the statement is false: a one-valued variable has the constant conditional distribution $1$, so its parent set, and its role as a parent, are invisible to every oracle. Assumption 1 holds by construction (see the definitions).
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Section 3, Theorem 1, p. 5; proof in Appendix C, pp. 21-23

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

theorem optimal_policies_identify_cbn {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (hk : ∀ i, 2 ≤ k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (paD paU : Finset ι) :
    ∃ F : UParam k A paU → Oracle k A →
        Set ι × (ι → Finset ι) × ((i : ι) → Cfg k → Fin (k i) → ℝ),
      ∀ pa : ι → Finset ι, IsAcyclic pa →
        ∀ᵐ θ : CPDParam k pa × UParam k A paU, ValidParam pa θ.1 →
          DomainDependent pa paD (utilOf paU θ.2) →
          ∀ O : Oracle k A, IsOptimalOracle paD (cpdOf pa θ.1) (utilOf paU θ.2) O →
            (F θ.2 O).1 = ancU pa paD paU ∧
            ∀ i ∈ ancU pa paD paU, (F θ.2 O).2.1 i = pa i ∧ (F θ.2 O).2.2 i = cpdOf pa θ.1 i := by sorry

end RobustAgentsCausal
