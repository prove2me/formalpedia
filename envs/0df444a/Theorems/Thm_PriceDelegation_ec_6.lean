-- Prove2me | Theorems.Thm_PriceDelegation_ec_6
-- name    : PriceDelegation.ec_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:37.500702+00:00
-- url     : https://prove2.me/theorems/f11c069a-d829-4286-bbee-60c35bfe7741
-- title:
--   (EC.6) — at the optimal reservation contract (IC) binds and the agent is indifferent on $(\lambda,\mu]$
-- statement:
--   Let $\psi>0$, $0\le\lambda\le\mu$ and $M$ be such that $t=t^M_{\lambda,\mu}$ solves the problem of Lemma 6. Then
--   $$
--   E[t(V)]-\psi=t(p)\,\bar F(p)\quad\text{for every }\lambda<p\le\mu,
--   $$
--   and $t(\varphi)\bar F(\varphi)\le E[t(V)]-\psi$ for every $\varphi>0$; so $E[t(V)]-\psi=\max_{\varphi>0}t(\varphi)\bar F(\varphi)$, attained at every price in $(\lambda,\mu]$.
--
--   This indifference is what lets the separable contract implement both learning and the uninformed price $\varphi^*(\lambda^{p-l})$ in Lemma 7.
--
--   Differences from the source:
--   - reading: (EC.6) for $\lambda\le p\le\mu^*$ → for $\lambda<p\le\mu$; reason: with the contract's value $0$ at $p=\lambda$ (proof of Lemma 6, p.ec10) the identity fails at $p=\lambda$; $\lambda$ is a null point of $V$
--   - reading: (10): $t^M_{\lambda,\mu}(p)=0$ for $p<\lambda$ and $M\bar F(\mu)/\bar F(p)$ for $\lambda\le p\le\mu$ (p.29) → $t^M_{\lambda,\mu}(p)=0$ for $p\le\lambda$, in particular $t(0)=0$; reason: (reservation) requires $t(p)=0$ for $p\le\lambda$ and the proof of Lemma 6 (p.ec10) writes "0, if $p\le\lambda$"; $t(0)=0$ is the paper's convention (pp.13, 28)
--   - encoding: (IC): $E[t(V)-\psi]\ge\max_{\varphi>0}\{t(\varphi)\bar F(\varphi)+t(0)F(\varphi)\}$ (p.10) → the bound at every $\varphi>0$; reason: a competitor contract need not attain the maximum; the bound at every point is the supremum
--   - generalization: a reservation price $\lambda>0$ (p.29) → any $\lambda\ge0$; reason: the multiplier $\lambda^*$ the contract uses can be $0$ (for $K=N$, $\lambda^{f-l}=0$); every $\lambda>0$ is included
--   - generalization: the standing Assumptions 1 and 2 of the paper → not assumed; reason: the statement holds without them; the paper's case is the special case where they hold
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), proof of Lemma 6, (EC.6), p.ec11

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- (EC.6) (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of
Sept. 22, 2021), proof of Lemma 6, p.ec11): if `t = t^M_{λ,µ}` solves the problem of Lemma 6, then
(IC) binds and the agent is indifferent among the uninformed prices in `(λ, µ]`:
`E[t(V)] − ψ = t(p) · F̄(p)` for `λ < p ≤ µ`, and `t(φ) · F̄(φ) ≤ E[t(V)] − ψ` for every `φ > 0`.

**Formalization Note** The page allows `p = λ`; at `p = λ` the contract is `0` (see `tRes`), so the
identity is stated for `p > λ`. -/
theorem ec_6 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {M lam μ : ℝ} (hlam : 0 ≤ lam) (hμ : lam ≤ μ)
    (hsol : SolvesRes V ψ M lam (tRes V M lam μ)) :
    (∀ p : ℝ, lam < p → p ≤ μ →
        expect V (tRes V M lam μ) - ψ = tRes V M lam μ p * Fbar V p) ∧
      ∀ φ : ℝ, 0 < φ → tRes V M lam μ φ * Fbar V φ ≤ expect V (tRes V M lam μ) - ψ := by sorry

end PriceDelegation
