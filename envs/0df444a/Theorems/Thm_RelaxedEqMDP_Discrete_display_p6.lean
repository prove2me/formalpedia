-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_display_p6
-- name    : RelaxedEqMDP.Discrete.display_p6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:45.826199+00:00
-- url     : https://prove2.me/theorems/3e37f1f0-a2be-4474-948e-642f8a12a1a8
-- title:
--   Display on p. 6 — $J^{\pi'\otimes_1\pi}_\lambda(i)=f^{\pi'(i)}(0,i)+\lambda\mathcal H(\pi'(i))+\mathbb E_i[V^\pi_\lambda(X^{\pi'}_1)]$
-- statement:
--   Throughout, $U\subset\mathbb R^\ell$ ($\ell\ge1$) is a compact action space with $\mathrm{Leb}(U)>0$, the state space is $\mathcal S=\{1,\dots,d\}$, $p^u=(p^u_{ij})$ is the transition matrix of the chain under action $u\in U$ with $i$-th row $p^u_i$, and $f(t,i,u)$ is the reward.
--
--   Let Assumption 2.1 hold, let $\lambda>0$, and let $\pi,\pi'\in\Pi_r$ be regular relaxed controls. Then for every initial state $i\in\mathcal S$, the entropy-regularized value of the concatenation $\pi'\otimes_1\pi$ ($\pi'$ at time $0$, $\pi$ afterwards) splits into the time-$0$ reward and entropy plus the expected auxiliary value at time $1$:
--   $$J^{\pi'\otimes_1\pi}_\lambda(i)=f^{\pi'(i)}(0,i)+\lambda\mathcal H(\pi'(i))+\sum_{j\in\mathcal S}p^{\pi'}_{ij}\,V^\pi_\lambda(j),$$
--   where $p^{\pi'}_{ij}=\int_U p^u_{ij}(\pi'(i))(du)$, so that the last sum is $\mathbb E_i[V^\pi_\lambda(X^{\pi'}_1)]$.
--
--   This is the identity from which the paper reads off the time-$0$ agent's best response (2.11) and proves Proposition 2.1.
--
--   **Formalization Note** $J^{\pi'\otimes_1\pi}_\lambda$ is defined from the control sequence $(\pi',\pi,\pi,\dots)$, so the identity is a genuine exchange of the infinite sum over time with the finite sum over $j$. Measurability of $u\mapsto f(t,i,u)$ and $u\mapsto p^u_{ij}$ is assumed (implicit in the integrals of the page).
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 6, display after (2.10) (first equality)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete

/-- Display on p. 6 (from (2.4) and (2.10)): for regular `π, π′`,
`J^{π′⊗₁π}_λ(i) = f^{π′(i)}(0,i) + λ ℋ(π′(i)) + E_i[V^π_λ(X^{π′}_1)]`, where the last term is
`∑ⱼ p^{π′}_{ij} V^π_λ(j)`. -/
theorem display_p6 {d ℓ : ℕ} (hℓ : 0 < ℓ) (U : Set (A ℓ)) (p : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℕ → Fin d → A ℓ → ℝ) (δ : ℕ → ℝ) (hS : Standing U p) (hM : MeasMaps f p)
    (h21 : Assumption21 U f δ) (lam : ℝ) (hlam : 0 < lam) (pol pol' : Control d ℓ)
    (hpol : IsRegular U pol) (hpol' : IsRegular U pol') (i : Fin d) :
    JlamSeq U p f δ lam (concat pol' pol) i =
      fbar f (pol' i) 0 i + lam * ent U (pol' i) +
        ∑ j, Pbar p pol' i j * Vlam U p f δ lam pol j := by sorry
end RelaxedEqMDP.Discrete
