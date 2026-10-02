-- Prove2me | Theorems.Thm_ServiceParts_UnitDecomp_lemma1_monotone_committed
-- name    : ServiceParts.UnitDecomp.lemma1_monotone_committed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:44:55.42399+00:00
-- url     : https://prove2.me/theorems/5456bb45-3975-4e1c-9ba6-15192d2637fd
-- title:
--   Lemma 1 — monotone policies are optimal, every monotone policy is committed, committed policies are optimal
-- statement:
--   Consider the system $\mathcal S$ over a horizon of $N$ periods, with Markov-modulated demand, lead time $m-1$, holding cost $h$, backorder cost $b$ ($0<h<b$) and discount factor $\alpha\in(0,1]$. Write $C^\pi_1(s,x_1)$ for the expected discounted cost of a policy $\pi$ in periods $1,\dots,N$ from Markov state $s$ and starting configuration $x_1$, and $V^{\mathcal S}_1(s,x_1)$ for the infimum over all policies. Then:
--
--   1. there is a monotone policy $\pi$ with
--   $$C^\pi_1(s,x_1) = V^{\mathcal S}_1(s,x_1)$$
--   for every Markov state $s$ and every starting configuration $x_1$;
--   2. every monotone policy is committed: along every realisation, unit $j$ is used exactly when customer $j$ is served;
--   3. there is a committed policy that is optimal in the same sense.
--
--   A class of policies is optimal when it contains an optimal policy; the lemma lets the rest of the analysis restrict attention to policies that pair unit $j$ with customer $j$.
--
--   **Formalization Note** Optimality is against all policies for $\mathcal S$, including non-monotone ones, and one policy is required to be optimal from every starting configuration simultaneously. Starting configurations are those built on pp. 23–24, which are monotone; units on hand are matched to waiting customers lowest index first, as the book assumes on p. 25.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 26, Lemma 1 (with the definitions of monotone and committed policies, p. 25)

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_System

namespace ServiceParts.UnitDecomp

theorem lemma1_monotone_committed {σ : Type} [Fintype σ] (M : Model σ) (N : ℕ) :
    (∃ π : SPolicy σ, M.IsMonotone π ∧
      ∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
        M.sysCost N π 1 s (M.initState a v₀) = M.sysOpt N 1 s (M.initState a v₀)) ∧
    (∀ π : SPolicy σ, M.IsMonotone π → M.IsCommitted π) ∧
    (∃ π : SPolicy σ, M.IsCommitted π ∧
      ∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
        M.sysCost N π 1 s (M.initState a v₀) = M.sysOpt N 1 s (M.initState a v₀)) := by sorry

end ServiceParts.UnitDecomp
