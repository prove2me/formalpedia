-- Prove2me | Theorems.Thm_PersuasionNetworks_theorem_1_solvable
-- name    : PersuasionNetworks.theorem_1_solvable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:34.844663+00:00
-- url     : https://prove2.me/theorems/0bc1e0e8-dcc6-43f6-8df5-e325d4abf7e7
-- title:
--   Proof of Theorem 1 — the system (9)–(10) is solvable
-- statement:
--   Let $(p,z)$ be feasible in (OPT) with C1–C4, and let $i\in[m]$ with $\bar L_i\cap P=\{k_1,k_2\}$, $k_1>k_2$. Then there are $t',t''\in[t_i,t_{i-1}]$ with $t'\le t''$ such that
--   $$
--   F(t')-F(t_i)+F(t_{i-1})-F(t'')=p_{k_1},\qquad
--   \int_{F(t_i)}^{F(t')}F^{-1}(x)\,dx+\int_{F(t'')}^{F(t_{i-1})}F^{-1}(x)\,dx=z_{k_1}.
--   $$
--
--   This is what makes Step S1 of Algorithm 1 succeed.
--
--   **Formalization Note** The numbers $t',t''$ are extended reals, as $t_i$ and $t_{i-1}$ may be infinite.
--
--   Differences from the source:
--   - encoding: the index i ∈ [m] and the sets L_i → a pair (e', e) of consecutive binding indices; reason: L_i = [e_i] for e_0 = 0 < e_1 < …; same data
--   - encoding: t′, t″ and F at infinite end points → extended reals and extCdf, with F(−∞) = 0 and F(+∞) = 1; reason: footnote 24 allows infinite end points
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Proof of Theorem 1, p.49

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism
import Definitions.Def_PersuasionNetworks_Algorithm1

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **(9)–(10) are solvable**, Candogan, SSRN 3346144 (preprint), Proof of Theorem 1, p.49: for a feasible solution with
C1–C4 and an index `i` with `L̄_i ∩ P = {k₁, k₂}`, `k₁ > k₂`, there are `t' ≤ t''` in `[t_i, t_{i-1}]`
satisfying (9) and (10), so that Step S1 of Algorithm 1 does not get stuck. -/
theorem theorem_1_solvable (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (p z : ℕ → ℝ) (hfeas : IsFeasible μ 𝒯 K b p z) (hC : SatisfiesC μ 𝒯 K p z)
    (e' e k₁ k₂ : ℕ) (hblock : IsBlock μ 𝒯 K p z e' e)
    (hactive : active p e' e = {k₁, k₂}) (hlt : k₂ < k₁) :
    ∃ t' t'' : EReal, SolvesS1 μ 𝒯 p z e' e k₁ t' t'' := by sorry

end PersuasionNetworks
