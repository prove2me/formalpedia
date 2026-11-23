-- Prove2me | Theorems.Thm_RobustAgentsCausal_causal_model_identifies_policies
-- name    : RobustAgentsCausal.causal_model_identifies_policies
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:35:28.776239+00:00
-- url     : https://prove2.me/theorems/d10e0d55-40f6-441e-b4e6-b5d82600a855
-- title:
--   Theorem 3: a (approximate) causal model identifies optimal (regret-bounded) policies
-- statement:
--   Let the chance variables take $k_i\ge1$ values, let the decision set be finite and nonempty, and fix the decision parents $\mathrm{Pa}_D$. There is a procedure $F$ that maps a causal Bayesian network $M=(P,G)$ over the chance variables, a utility $U(d,\bm c)$ (so $\mathrm{Pa}_U\subseteq\bm C\cup\{D\}$) and a soft intervention $\sigma$ to a policy, with the following properties.
--
--   1. If $\sigma$ is a soft intervention compatible with $G$, then $F(M,U,\sigma)$ is an optimal policy $\pi^*_\sigma(d\mid\mathrm{pa}_D)$ in $M(\sigma)$.
--   2. For every such $M$, $U$ and $\sigma$ there are constants $C$ and $\epsilon_0>0$ such that the following holds for every $0\le\epsilon\le\epsilon_0$. If $M'=(P',G')$ is any causal Bayesian network with $|P'(v_i\mid\mathrm{pa}_i)-P(v_i\mid\mathrm{pa}_i)|\le\epsilon$ for all $i$ and all states, then the policy $F(M',U,\sigma)$ has regret at most $C\epsilon$ in $M(\sigma)$.
--
--   Together with Theorem 2, this says that an approximate causal model is necessary and sufficient for regret-bounded policies under local interventions.
--
--   **Formalization Note** "$\epsilon\ll1$" and "regret grows linearly in $\epsilon$" are read as a bound $C\epsilon$ for $\epsilon$ in some interval $[0,\epsilon_0]$, with $C$ and $\epsilon_0$ depending on $M$, $U$ and $\sigma$. The policies have input $\mathrm{Pa}_D$. Conditional distributions of $M$ and $M'$ are compared at every joint state of the chance variables.
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Section 3.1, Theorem 3, p. 6; proof in Appendix E, p. 29

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

theorem causal_model_identifies_policies {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (paD : Finset ι) :
    ∃ F : (ι → Finset ι) → ((i : ι) → Cfg k → Fin (k i) → ℝ) → (A → Cfg k → ℝ) → SoftInt k →
        Cfg k → A → ℝ,
      (∀ (pa : ι → Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ), IsAcyclic pa → IsCPD pa P →
        ∀ (u : A → Cfg k → ℝ) (σ : SoftInt k), σ.IsCompatible pa →
          IsOptimal paD (softJoint P σ) u (F pa P u σ)) ∧
      (∀ (pa : ι → Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ), IsAcyclic pa → IsCPD pa P →
        ∀ (u : A → Cfg k → ℝ) (σ : SoftInt k), σ.IsCompatible pa →
          ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
            ∀ (pa' : ι → Finset ι) (P' : (i : ι) → Cfg k → Fin (k i) → ℝ),
              IsAcyclic pa' → IsCPD pa' P' → (∀ i c v, |P' i c v - P i c v| ≤ ε) →
                IsDeltaOptimal (C * ε) paD (softJoint P σ) u (F pa' P' u σ)) := by sorry

end RobustAgentsCausal
