-- Prove2me | Theorems.Thm_QuadBogolyubov_proposition_4_4
-- name    : QuadBogolyubov.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:07:15.693204+00:00
-- url     : https://prove2.me/theorems/d1f2ea25-8f00-4748-ad63-4d982b7e1e97
-- title:
--   Proposition 4.4 — relative counting lemma
-- statement:
--   There is a constant $C>0$ such that the following holds. Let $0<\varepsilon\le1/2$, $d\in\mathbb N$, and let $W_0\subseteq\mathbb F_2^n$ be a quadratic variety containing $0$, of complexity $(0,d)$ and rank $\mathrm{rk}(W_0)\ge C(d+\log_2(1/\varepsilon))$. Then for all $f_1,\dots,f_7:\mathbb F_2^n\to[-1,1]$ supported on $W_0$,
--   $$|\Lambda(f_1,\dots,f_7)|\le\Big(\min_{i\in[7]}\|f_i\|_{U^3(W_0)}+\varepsilon\Big)\Lambda(\mathbf 1_{W_0}).$$
--   This is the local counting lemma: the $U^3(W_0)$ norm controls the count of punctured cubes in a high-rank variety.
--
--   **Formalization Note** The real functions are cast to complex ones in the local norm; the minimum over `Fin 7` is `⨅ i`.
--
--   Differences from the source:
--   - reading: log → log₂ (`Real.logb 2`); reason: Appendix D writes log₂; the base only moves the constant
--   - encoding: rk(W) as a number, the minimum over λ ≠ 0 → `HasRankAtLeast W r` for a real lower bound r, vacuous when d₂ = 0; reason: p.68: "When q = 0, we say by convention that the rank is infinite"; a minimum over the empty set has no number in ℝ or ℕ
--   - reading: "λ₀ + λ₁q₁ + ⋯ + λ_{d₂}q_{d₂} is not a linear function for any (λ₀, …, λ_{d₂}) ≠ 0" (§3, p.9) → `QuadVariety.q_indep`: for every λ ≠ 0, Σλⱼqⱼ agrees on V with no polynomial of degree ≤ 1; reason: as printed the condition fails for λ = (1, 0, …, 0), so no variety would exist; the same sentence names the intent, "quadratic parts are linearly independent"
--   - encoding: qⱼ : V → F₂ quadratic functions on V → global quadratic polynomials on F₂ⁿ, used only on V; reason: p.68: each quadratic function on V extends to a quadratic polynomial on F₂ⁿ
--   - encoding: min_{i∈[7]} → `⨅ i : Fin 7`; reason: the infimum of a real family over a non-empty finite type is its minimum
--   - encoding: F₂ⁿ → Fin n → ZMod 2; reason: Lean convention; the same set
-- source:
--   Castro-Silva, Golovnev, Gur, Wolf, A Quadratic Bogolyubov Theorem and Quantum Worst-Case to Average-Case Reductions, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Proposition 4.4, p.11; proof App. D.3, pp.64–65

import Mathlib
import Definitions.Def_QuadBogolyubov_HasRankAtLeast
import Definitions.Def_QuadBogolyubov_gowersU3
import Definitions.Def_QuadBogolyubov_Lam

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace QuadBogolyubov

/-- **Proposition 4.4 (Relative counting lemma).** There is a constant `C > 0` such that for every
`0 < ε ≤ 1/2`, `d ∈ ℕ` and every quadratic variety `W₀ ∋ 0` of complexity `(0, d)` with
`rk(W₀) ≥ C(d + log₂(1/ε))`, all `f₁, …, f₇ : 𝔽₂ⁿ → [−1, 1]` supported on `W₀` satisfy
`|Λ(f₁, …, f₇)| ≤ (min_{i∈[7]} ‖fᵢ‖_{U³(W₀)} + ε) Λ(1_{W₀})`.

Castro-Silva, Golovnev, Gur, Wolf, *A Quadratic Bogolyubov Theorem and Quantum Worst-Case to
Average-Case Reductions*, STOC 2027 submission (held manuscript, sha256 9d91dee3…), Proposition 4.4, p.11: "There exists a constant C > 0 such that the following holds. Let
0 < ε ≤ 1/2, d ∈ N, and let W0 ⊆ F₂ⁿ be a quadratic variety that contains 0, has complexity
(0, d) and rank rk(W0) ≥ C(d+log(1/ε)). Then, for any bounded functions f1, . . . , f7 :
F₂ⁿ → [−1, 1] supported on W0, we have |Λ(f1, . . . , f7)| ≤ (min_{i∈[7]} ∥fi∥U3(W0) + ε)Λ(1W0)."

**Formalization Note.** The seven functions are `f : Fin 7 → 𝔽₂ⁿ → ℝ` (`f 0, …, f 6` are
`f₁, …, f₇`), real-valued, used as complex functions in the local norm. The minimum over the
finite non-empty index set `Fin 7` is `⨅ i`. `log` is `log₂`. -/
theorem proposition_4_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ (n d : ℕ) (W₀ : QuadVariety n),
        (0 : Fin n → ZMod 2) ∈ W₀.carrier → W₀.d1 = 0 → W₀.d2 = d →
        HasRankAtLeast W₀ (C * ((d : ℝ) + Real.logb 2 (1 / ε))) →
        ∀ f : Fin 7 → (Fin n → ZMod 2) → ℝ, (∀ i x, |f i x| ≤ 1) →
          (∀ i x, x ∉ W₀.carrier → f i x = 0) →
          |Lam f| ≤ ((⨅ i : Fin 7, localU3 W₀ (fun x => (f i x : ℂ))) + ε) *
            Lam (fun _ => ind W₀.carrier) := by sorry

end QuadBogolyubov
