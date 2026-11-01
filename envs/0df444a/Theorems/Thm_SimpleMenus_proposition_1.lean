-- Prove2me | Theorems.Thm_SimpleMenus_proposition_1
-- name    : SimpleMenus.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:39:06.19644+00:00
-- url     : https://prove2.me/theorems/49dc9262-9dd5-4f05-9e7d-c5e980a4ecd9
-- title:
--   Proposition 1 (corrected: constraint qualification) — the competitive ratio equals the value of Problem (3)
-- statement:
--   Assume Assumption 1 and the constraint qualification. Let $n\ge1$.
--
--   1. For every $n$-level mechanism $\pi\in\Pi_n$ (price levels $v_1\le\dots\le v_n$ in $[0,\bar v]$, probabilities $x$ in the simplex), the competitive ratio $\mathrm{CR}(\pi)$ equals the value of Problem (3) at $\pi$, i.e. the supremum of $r\in\mathbb R$ such that some $\lambda\in\mathbb R_+^{K\times[0,\bar v]}$ satisfies
--   $$\sum_{k=1}^K\phi_k(w)\lambda_k(p)\le t(w)\ \ \forall p\in[0,\bar v],\ w\in[0,p),\qquad r\cdot p+\sum_{k=1}^K\phi_k(w)\lambda_k(p)\le t(w)\ \ \forall p\in[0,\bar v],\ w\in[p,\bar v].$$
--   2. Consequently the robust problem (1) and Problem (3) have the same optimal value:
--   $$\sup_{\pi\in\Pi_n}\mathrm{CR}(\pi)=\sup_{\pi\in\Pi_n}\ \sup\{r:\ (r,\lambda)\text{ feasible in (3) at }\pi\}.$$
--
--   This turns the max-min ratio problem into a maximization with linear constraints for each fixed mechanism.
--
--   **Formalization Note** Values are extended reals; the competitive ratio ranges over the laws with positive benchmark.
--
--   Differences from the source:
--   - correction: no condition beyond Assumption 1 → ConstraintQualification: every ϕ_k is a step function, or some F₀ ∈ 𝓕 has ∫ ϕ_k dF₀ > 0 for every non-step ϕ_k; reason: the printed statement is false: K = 1, 0 < c < v̄, ϕ(w) = min(w − c, 0), V = {c}, x = 1 satisfies Assumption 1 with CR = c/v̄ but (3) and (4) have value 0, and at p ∈ (0, c] the homogenized primal is c while its dual is 0
--   - reading: Problem (1) is equivalent to Problem (3), where the optimal solution r is the optimal competitive ratio and π the corresponding optimal price density → (a) CR(π) = value3(π) for every π ∈ Π_n, and (b) sup_{π∈Π_n} CR(π) = sup_{π∈Π_n} value3(π); reason: the proof works for each fixed π; (b) is the equality of optimal values, and (a) makes "r is the competitive ratio of π" precise
--   - reading: Assumption 1 (bounded, piecewise continuous with finite segments, nondecreasing within each segment) → Assumption1: bounded on [0,v̄], and a finite P ⊆ [0,v̄] per k with ϕ_k continuous and monotone on every open piece cut by P; reason: broadest reading of "finite segments"; values at the breakpoints are free
--   - generalization: k = 1, …, K → ϕ : Fin K → ℝ → ℝ with K = 0 allowed; reason: K = 0 is the set of all laws on [0,v̄]; every K ≥ 1 is included
--   - encoding: λ ∈ ℝ_+^{K×[0,v̄]} → λ : ℝ → Fin K → ℝ, nonnegative everywhere; reason: only the values on [0,v̄] enter the constraints
--   - encoding: real optimal values, infima and suprema → EReal values (⊤ for an unbounded supremum or an empty infimum); reason: Lean convention; avoids the junk value 0 of real sSup/sInf on unbounded or empty sets
--   - encoding: CR(π) = inf_{F∈𝓕} Rev(π,F)/Rev(OPT,F) → infimum over F ∈ 𝓕 with Rev(OPT,F) > 0; reason: a law with Rev(OPT,F) = 0 has Rev(π,F) = 0, the ratio 0/0; (EC.1) imposes nothing on it
--   - encoding: t(v) = ∫_0^v π(u)u du with π = Σ x_i δ(v − v_i) → pay v x w = Σ_{v_l ≤ w} x_l v_l; reason: closed form of the Dirac integral (p.ec8); the atom at w is included, the buyer buys at the posted price
--   - encoding: F ∈ P([0, v̄]), constraints ∫ ϕ_k dF ≥ 0 → Borel probability measure on ℝ with F([0,v̄]ᶜ) = 0, and Integrable (ϕ k) F in each constraint; reason: same laws; integrability holds for every such law when ϕ_k is bounded and piecewise monotone
--   - encoding: Rev(OPT,F) = max_{p≥0} p(1 − F(p−)) → supremum over p ∈ [0, v̄] of p·F([p,∞)); reason: F is carried by [0,v̄], so prices above v̄ earn 0; the maximum is attained and only its value is used
--   - encoding: π ∈ Π_n → v : Fin n → ℝ monotone with values in [0,v̄], x ∈ stdSimplex ℝ (Fin n); reason: the paper's parametrization of Π_n (p.9); x_i ∈ [0,1] follows from the simplex
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, Proposition 1, p.10

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_rev
import Definitions.Def_SimpleMenus_opt
import Definitions.Def_SimpleMenus_ambiguitySet
import Definitions.Def_SimpleMenus_CR
import Definitions.Def_SimpleMenus_IsPiece
import Definitions.Def_SimpleMenus_Assumption1
import Definitions.Def_SimpleMenus_ConstraintQualification
import Definitions.Def_SimpleMenus_value3

open MeasureTheory Set

namespace SimpleMenus

/-- **Proposition 1** (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, p.10), with the constraint qualification added: under
Assumption 1 and `ConstraintQualification`, for every `n ≥ 1`,
1. for every `n`-level mechanism `(v, x)` (`v_1 ≤ ⋯ ≤ v_n` in `[0, v̄]`, `x` in the simplex) the
   competitive ratio equals the value of Problem (3) at that mechanism: `CR(π) = value3(π)`;
2. the optimal values agree: `sup_{π ∈ Π_n} CR(π) = sup_{π ∈ Π_n} value3(π)`.

Formalization Note: values in `EReal`; `CR` ranges over the laws with `Rev(OPT, F) > 0`.
`ConstraintQualification` is a correction (CE1, see its docstring: `CR = c / v̄`, (3) has value
`0`). -/
theorem proposition_1 (vbar : ℝ) {K : ℕ} (phi : Fin K → ℝ → ℝ) (hA : Assumption1 vbar phi)
    (hCQ : ConstraintQualification vbar phi) (n : ℕ) (hn : 1 ≤ n) :
    (∀ v x : Fin n → ℝ, Monotone v → (∀ i, v i ∈ Icc 0 vbar) → x ∈ stdSimplex ℝ (Fin n) →
      CR vbar phi v x = value3 vbar phi v x) ∧
    (⨆ (v : Fin n → ℝ) (x : Fin n → ℝ)
        (_ : Monotone v ∧ (∀ i, v i ∈ Icc 0 vbar) ∧ x ∈ stdSimplex ℝ (Fin n)),
        CR vbar phi v x) =
      ⨆ (v : Fin n → ℝ) (x : Fin n → ℝ)
        (_ : Monotone v ∧ (∀ i, v i ∈ Icc 0 vbar) ∧ x ∈ stdSimplex ℝ (Fin n)),
        value3 vbar phi v x := by sorry

end SimpleMenus
