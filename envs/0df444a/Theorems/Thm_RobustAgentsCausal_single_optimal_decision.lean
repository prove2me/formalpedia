-- Prove2me | Theorems.Thm_RobustAgentsCausal_single_optimal_decision
-- name    : RobustAgentsCausal.single_optimal_decision
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:32:54.08948+00:00
-- url     : https://prove2.me/theorems/996ef14d-ec95-47cf-afa3-d69d2d93aa8a
-- title:
--   Lemma 3 (as proved): a single optimal decision in every possible context
-- statement:
--   Fix a DAG $G$ on the chance variables (each with $k_i\ge1$ values), a finite nonempty decision set, decision parents $\mathrm{Pa}_D$, utility parents $D$ and $\mathrm{Pa}_U$, and a local intervention $\sigma=\mathrm{do}(C_1=f_1(c_1),\dots,C_N=f_N(c_N))$. Then for Lebesgue-almost every parameter $(\theta_P,\theta_U)$ with $\theta_P$ valid, the following holds. For every context $\mathrm{pa}_D$ with $P(\mathrm{pa}_D;\sigma)>0$ there is exactly one decision $d$ maximising
--
--   $$\sum_{\bm z}U(d,\bm x)\,P(\bm z,\mathrm{pa}_D;\sigma)=P(\mathrm{pa}_D;\sigma)\,\mathbb E[u\mid\mathrm{pa}_D,\mathrm{do}(D=d);\sigma],$$
--
--   where $\bm Z=\bm C\setminus\mathrm{Pa}_D$. Hence the optimal policy in $M(\sigma)$ is deterministic and unique on every context of positive probability.
--
--   **Formalization Note** The paper states that there is a single deterministic optimal policy. That claim fails whenever $\sigma$ gives some context probability $0$, for example a hard intervention on a variable of $\mathrm{Pa}_D$, since any decision is then optimal in that context. The proof establishes uniqueness on contexts of positive probability, which is what is stated.
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Appendix C, Lemma 3 and its proof, eqs. (7)-(9), p. 20

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

theorem single_optimal_decision {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (pa : ι → Finset ι) (hpa : IsAcyclic pa) (paD paU : Finset ι) (f : LocalInt k) :
    ∀ᵐ θ : CPDParam k pa × UParam k A paU, ValidParam pa θ.1 →
      ∀ c₀ : Cfg k, 0 < ctxProb (localJoint (cpdOf pa θ.1) f) paD c₀ →
        ∃! d : A, ∀ d' : A,
          ctxUtil (localJoint (cpdOf pa θ.1) f) (utilOf paU θ.2) paD c₀ d' ≤
            ctxUtil (localJoint (cpdOf pa θ.1) f) (utilOf paU θ.2) paD c₀ d := by sorry

end RobustAgentsCausal
