-- Prove2me | Theorems.Thm_RobustAgentsCausal_domain_dependence_consequences
-- name    : RobustAgentsCausal.domain_dependence_consequences
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:32:16.314549+00:00
-- url     : https://prove2.me/theorems/bc8f8a27-3cf4-473e-a03e-cc3053372363
-- title:
--   Lemma 1: consequences of domain dependence
-- statement:
--   Let the chance variables $C_i$ take $k_i\ge1$ values, let the decision set $\mathcal A$ be finite and nonempty, let $G$ be a DAG on the chance variables, let $D$ have parents $\mathrm{Pa}_D$, and let the utility $U(d,x)$ depend on $d$ and the chance variables $\mathrm{Pa}_U$. Suppose the task is domain dependent (Assumption 2). Then
--
--   1. there is no decision $d$ with $d\in\arg\max_{d'}U(d',c)$ for every joint state $c$;
--   2. $\mathrm{Pa}_D\subsetneq\mathrm{Anc}_U$, where $\mathrm{Anc}_U$ denotes the chance variables that are ancestors of $U$;
--   3. $D\in\mathrm{Pa}_U$: there are $c$, $d$, $d'$ with $U(d,c)\ne U(d',c)$.
--
--   These facts give the decision task enough structure for the policy oracle to reveal information about the environment.
--
--   **Formalization Note** In the paper $\mathrm{Anc}_U$ also contains $D$, which would make (ii) trivial. The statement is therefore made for the chance variables of $\mathrm{Anc}_U$, as in the paper's proof. The model always lists $D$ as an argument of $U$, so (iii) is stated as the condition that $U$ actually depends on $d$.
-- source:
--   Richens and Everitt, Robust agents learn causal world models, ICLR 2024, arXiv:2402.10877v7, Appendix A.1, Lemma 1 (i)-(iii), with Assumptions 1-2 (Section 2.2-2.3), p. 16

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

theorem domain_dependence_consequences {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (pa : ι → Finset ι) (hpa : IsAcyclic pa) (paD paU : Finset ι) (uθ : UParam k A paU)
    (hdd : DomainDependent pa paD (utilOf paU uθ)) :
    (¬ ∃ d : A, ∀ c : Cfg k, ∀ d' : A, utilOf paU uθ d' c ≤ utilOf paU uθ d c) ∧
    ((↑paD : Set ι) ⊂ ancU pa paD paU) ∧
    (∃ (c : Cfg k) (d d' : A), utilOf paU uθ d c ≠ utilOf paU uθ d' c) := by sorry

end RobustAgentsCausal
