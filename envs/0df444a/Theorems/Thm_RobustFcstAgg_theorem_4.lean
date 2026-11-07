-- Prove2me | Theorems.Thm_RobustFcstAgg_theorem_4
-- name    : RobustFcstAgg.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:02:46.335462+00:00
-- url     : https://prove2.me/theorems/5397f807-491b-4c83-993e-b8f2f783dfad
-- title:
--   Theorem 4 — the minimum error is $1-\Theta(d^2/n)$ for $d=o(\sqrt n)$, $1-\Omega(1)$ for $d=\Theta(\sqrt n)$, and $O(e^{-4d/\sqrt n})$ for $d=\Omega(\sqrt n)$
-- statement:
--   Let $d=d(n)$ be any sequence of natural numbers, and let $v(n)=\min_{A\in\mathcal A^{\mathrm{ord}}_{d(n)}}\mathrm{error}(A)$, the least error of a randomized aggregation rule of agent and order complexity at most $d(n)$. For all large $n$ this minimum exists, and:
--
--   1. if $d=o(\sqrt n)$, there are $c_1,c_2>0$ with, for all large $n$,
--   $$1-c_2\frac{d^2}{n}\le v(n)\le1-c_1\frac{d^2}{n};$$
--   2. if $d=\Theta(\sqrt n)$, there is $c>0$ with $v(n)\le1-c$ for all large $n$;
--   3. if $d=\Omega(\sqrt n)$, there is $C>0$ with, for all large $n$,
--   $$v(n)\le C\,e^{-4d/\sqrt n}.$$
--
--   There is a phase transition at $d\approx\sqrt n$: below it the error tends to the trivial value $1$ when $d=o(\sqrt n)$, and above it the error vanishes when $d=\omega(\sqrt n)$.
--
--   **Formalization Note** The sequence may vanish at some $n$; $d=0$ gives error $1$.
--
--   Differences from the source:
--   - reading: Θ, Ω, O in d and n → a sequence d : ℕ → ℕ, with the constants chosen after d and before n; reason: the source's notation, in its strongest reading
--   - reading: min error = 1 − Ω(1) → min error ≤ 1 − c for all large n; reason: error ≤ 1 is the only content of the other side
--   - reading: Condition 1 is imposed on every query elicitable with respect to any finite set of random variables (pp.14, 25) → Condition 1 is a clause of the class, on the variables scored on the eliciting DAG's edges; reason: the clause is weaker on the class, so the lower bound is at least as strong; the upper-bound rules satisfy it
--   - reading: a payment function π(r, R) exists (Definition 2) → one π for all instances D; reason: the principal does not know D (p.4); it matters only for the upper-bound class, which uses the quadratic score
--   - reading: the expectations E_D[π(r, R) | S_i] (Definition 2) and E[(A − Y)²] (Eq. (1)) → the payment is integrable on a.e. fibre for every report r, and in the class A^ord_d the randomized output is jointly a.e.-measurable in (z, signals); reason: the expectations the source writes presuppose both; the linear intersection rules satisfy both
--   - encoding: approximators A, [n], E[· | S_i], the law of (A, Y) and X_∅ = 0 → rules, whose error depends only on the a.s. class of the output; Fin n; integrals over the hidden signals; lintegrals in ℝ≥0∞; nonempty T only; reason: same instances; conditioning is by independence of the signals
--   - encoding: the minimum is a real number in [0, 1] → ∃ v : ℝ, 0 ≤ v, with ENNReal.ofReal v the least element of errorSet; reason: the error is valued in ℝ≥0∞; 0 ≤ v stops ofReal from hiding a negative value
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Theorem 4, p.12

import Mathlib
import Definitions.Def_RobustFcstAgg_errorSet
open Filter Asymptotics

namespace RobustFcstAgg

/-- **Theorem 4.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Theorem 4, p.12: if `d = o(√n)`, `min_{A ∈ A^ord_d} error(A) = 1 − Θ(d²/n)`; if `d = Θ(√n)`, it is `1 − Ω(1)`; if
`d = Ω(√n)`, it is `O(e^{−4d/√n})`.

**Formalization Note.** `d` is a sequence in `n`, and the constants come after `d` and before `n`. The sequence may vanish at some `n`;
`d = 0` gives error `1`. `v` is the attained minimum, with `0 ≤ v` so that `ENNReal.ofReal v` does not hide a negative value. -/
theorem theorem_4 (d : ℕ → ℕ) :
    ((fun n => (d n : ℝ)) =o[atTop] (fun n : ℕ => √(n : ℝ)) →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N, ∀ n ≥ N, ∃ v : ℝ, 0 ≤ v ∧
        IsLeast (errorSet n (d n)) (ENNReal.ofReal v) ∧
        1 - c₂ * (d n : ℝ) ^ 2 / n ≤ v ∧ v ≤ 1 - c₁ * (d n : ℝ) ^ 2 / n) ∧
    ((fun n => (d n : ℝ)) =Θ[atTop] (fun n : ℕ => √(n : ℝ)) →
      ∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n ≥ N, ∃ v : ℝ, 0 ≤ v ∧
        IsLeast (errorSet n (d n)) (ENNReal.ofReal v) ∧ v ≤ 1 - c) ∧
    ((fun n : ℕ => √(n : ℝ)) =O[atTop] (fun n => (d n : ℝ)) →
      ∃ C : ℝ, 0 < C ∧ ∃ N, ∀ n ≥ N, ∃ v : ℝ, 0 ≤ v ∧
        IsLeast (errorSet n (d n)) (ENNReal.ofReal v) ∧
        v ≤ C * Real.exp (-4 * (d n : ℝ) / √(n : ℝ))) := by sorry

end RobustFcstAgg
