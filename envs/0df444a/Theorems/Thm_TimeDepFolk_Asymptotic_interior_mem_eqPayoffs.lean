-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_interior_mem_eqPayoffs
-- name    : TimeDepFolk.Asymptotic.interior_mem_eqPayoffs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:21.771331+00:00
-- url     : https://prove2.me/theorems/a17d802b-518d-4f88-9387-c242c16b26c1
-- title:
--   §5.1, pp. 17, 19, 26 — for patient θ^k, every x ∈ int F is a subgame perfect equilibrium payoff of Γ_{θ^k} for all large k
-- statement:
--   Consider a repeated game with finite nonempty player set $I$, finite nonempty action sets $A^i$ and stage payoffs $g$, with $\operatorname{int}\mathcal F\ne\emptyset$. Let $(\theta^k)_{k\ge1}$ be a sequence of patient evaluations. Then for every $x\in\operatorname{int}\mathcal F$ there is $K$ such that
--   $$x\in E_{\theta^k}\qquad\text{for all } k\ge K,$$
--   that is, for each $k\ge K$ some subgame perfect equilibrium $\sigma$ of $\Gamma_{\theta^k}$ has $\gamma_{\theta^k}(\sigma)=x$.
--
--   This is the content of the equilibrium construction of §5.1 (main path, punishment and reward phases): the main path reaches $x$ exactly, and no one-shot deviation is profitable once $k$ is large.
--
--   **Formalization Note.** The payoff is exactly $x$: Phase I follows a path $\mathbf x[0]$ with $\gamma_{\theta^k}(\mathbf x[0])=w[z_0]=x$ (p. 19). The closing sentence of p. 26 says only "$\eta$-close", which is weaker than what the construction gives; the exact statement is the one formalized. `eqPayoffs` uses subgame perfection with deviations over all behavior strategies.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), §5.1, pp. 17–26 (p. 17 'Let x be a payoff vector in the interior of F'; p. 19; p. 26)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem interior_mem_eqPayoffs {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (hint : (interior (F g)).Nonempty)
    (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    ∀ x ∈ interior (F g), ∃ K : ℕ, ∀ k ≥ K, x ∈ eqPayoffs g (θ k) := by sorry

end TimeDepFolk.Asymptotic
