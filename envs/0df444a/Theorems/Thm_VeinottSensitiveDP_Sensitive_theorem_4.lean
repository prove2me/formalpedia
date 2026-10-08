-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_theorem_4
-- name    : VeinottSensitiveDP.Sensitive.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:50.555976+00:00
-- url     : https://prove2.me/theorems/b3348374-fe2f-4bf9-a321-e031ed99783e
-- title:
--   Theorem 4 — no improvement of order n+1 implies n^± discount optimality, which rules out improvement of order n
-- statement:
--   In the model of §4, where every $P(f)$ is substochastic (and, for the sign $-$, every stationary policy is transient), let $S$ be the number of states, $f\in F$ and $n\in\{-2,-1,\dots,S-1\}$.
--
--   1. If $G_{n+1}^\pm(f)$ is empty, then $f\in D_n^\pm$.
--   2. If $f\in D_n^\pm$, then $G_n^\pm(f)$ is empty.
--
--   Here $D_n^\pm$ is the set of decision rules $f$ whose stationary policy $f^\infty$ satisfies $\liminf_{\rho\to0\pm}|\rho|^{-n}[V_\rho(f^\infty)-V_\rho(\pi)]\ge0$ for all policies $\pi$ ($D_{-2}=F$), and $G_n^\pm(f)=\{g:\Psi_n^\pm(g,f)\succ0\}$ is the set of improvements of $f$ of order $n$.
--
--   The theorem gives a test for $n^\pm$ discount optimality that only inspects the finitely many one-step switches $g$, and it lets the policy improvement method stop as soon as no improvement of order $n+1$ is left.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. The liminf is encoded per state as "for every $\varepsilon>0$, eventually $\ge-\varepsilon$"; the lexicographic order is applied row by row.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1648, §4, Theorem 4

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Theorem 4: suppose `f ε F` and `n = −2, −1, ⋯, S − 1`.
1°. If `G_{n+1}^±(f)` is empty, then `f ε D_n^±`.
2°. If `f ε D_n^±`, then `G_n^±(f)` is empty.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1648, §4, Theorem 4.

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`; the `−` case assumes the transient case, where alone `n⁻`
discount optimality is defined (p. 1644). `S = Fintype.card St`. `D_n^±` is the set of `f` whose
stationary policy `f^∞` is `n^±` discount optimal against **all** policies (27), with `D_{−2} = F`;
`G_n^±(f) = {g : Ψ_n^±(g, f) ≻ 0}` (lexicographic, columns `−1, …, n`), empty for `n < −1`. -/
theorem theorem_4 {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (htr : σ = -1 → M.TransientCase) (n : ℤ) (hn1 : -2 ≤ n)
    (hn2 : n ≤ (Fintype.card St : ℤ) - 1) (f : DecisionRule A) :
    (M.G σ (n + 1) f = ∅ → f ∈ M.D σ n) ∧ (f ∈ M.D σ n → M.G σ n f = ∅) := by sorry

end VeinottSensitiveDP.Sensitive
