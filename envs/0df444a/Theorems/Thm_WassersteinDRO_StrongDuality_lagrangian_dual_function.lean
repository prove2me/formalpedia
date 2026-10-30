-- Prove2me | Theorems.Thm_WassersteinDRO_StrongDuality_lagrangian_dual_function
-- name    : WassersteinDRO.StrongDuality.lagrangian_dual_function
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:38.617921+00:00
-- url     : https://prove2.me/theorems/f8b206e9-3a6b-42b7-94b4-125f5b9bf4ac
-- title:
--   The objective of (10) is the Lagrangian dual function of the worst-case risk problem (6)
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra (the paper's $\mathbb R^m$ with an arbitrary norm). Let $p \ge 1$, let $\Xi \subseteq E$ be closed, let $\mathbb P$ be a Borel probability measure on $E$ with $\mathbb P(E \setminus \Xi) = 0$ (the nominal distribution $\widehat{\mathbb P}_N$), and let $\ell : E \to [-\infty, +\infty]$ be upper semicontinuous with $\int |\ell| \, \mathrm d\mathbb P < \infty$ (Assumption 1 of the paper). Let $\varepsilon \ge 0$, and write $\ell_\gamma(\xi) = \sup_{z \in \Xi} \ell(z) - \gamma\|z - \xi\|^p$. For every Lagrange multiplier $\gamma \ge 0$:
--
--   1. (dual function) the supremum of the Lagrangian of (6) over all $\mathbb Q \in \mathcal P(\Xi)$ with $W_p(\mathbb Q, \mathbb P) < \infty$ equals the objective of (10) at $\gamma$:
--   $$\sup_{\substack{\mathbb Q \in \mathcal P(\Xi) \\ W_p(\mathbb Q, \mathbb P) < \infty}} \Big( \mathbb E^{\mathbb Q}[\ell(\xi)] - \gamma \big( W_p(\mathbb Q, \mathbb P)^p - \varepsilon^p \big) \Big) = \mathbb E^{\mathbb P}[\ell_\gamma(\xi)] + \gamma \varepsilon^p;$$
--   2. (weak duality) $\mathcal R_{\varepsilon,p}(\mathbb P, \ell) \le \mathbb E^{\mathbb P}[\ell_\gamma(\xi)] + \gamma \varepsilon^p$.
--
--   All expectations follow the paper's convention ($+\infty$ when the positive part is not integrable) and all values lie in $[-\infty, +\infty]$. This is the paper's statement that the right-hand side of (10) is the Lagrangian dual of (6) with multiplier $\gamma$ for the constraint $W_p(\mathbb Q, \mathbb P) \le \varepsilon$; that the dual and primal values coincide is Theorem 7 itself.
--
--   **Formalization Note** The constraint is dualized in the form $W_p^p \le \varepsilon^p$, as the term $\gamma\varepsilon^p$ of (10) requires. Measures with $W_p(\mathbb Q, \mathbb P) = \infty$ are left out of the supremum so that the subtracted term is a real number; they would give the Lagrangian the value $-\infty$ when $\gamma > 0$, and at most $\sup_\Xi \ell$, which the finite-distance measures already approach, when $\gamma = 0$.
--
--   Differences from the source:
--
--   - reading: 'the minimization problem on the right hand side of (10) can indeed be identified with the strong Lagrangian dual of problem (6)' → (a) for each γ ≥ 0 the supremum over Q of the Lagrangian R(Q, ℓ) − γ(W_p(Q, P)^p − ε^p) equals E^P[ℓ_γ] + γε^p, and (b) R_{ε,p}(P, ℓ) ≤ E^P[ℓ_γ] + γε^p; reason: a Lagrangian dual is the infimum over multipliers of the dual function, and it bounds the primal; strong duality (equality of values) is Theorem 7, the goal
--   - reading: the Wasserstein constraint W_p(Q, P̂N) ≤ ε with multiplier γ → the constraint dualized as W_p(Q, P)^p ≤ ε^p; reason: the term γε^p in (10) fixes the p-th power form
--   - encoding: the Lagrangian maximized over Q ∈ P(Ξ) → the supremum over Q ∈ P(Ξ) with W_p(Q, P) < ∞; reason: Q with W_p = ∞ contribute −∞ when γ > 0 and nothing beyond sup_Ξ ℓ = ℓ_0 when γ = 0, which finite-distance Q already approach; no value changes
--   - generalization: the nominal distribution P̂N (empirical (3) or elliptical (4), Example 1, p. 2) → any Borel probability measure P on E with P(Ξᶜ) = 0; reason: the paper's nominals are instances; the statement specializes to them
--   - reading: Ξ closed, 'known to contain the support of P' (p. 6); P̂N built from samples of P → hypothesis hPΞ : P Ξᶜ = 0 on the nominal distribution; reason: p. 6 calls B_{ε,p}(P̂N) the ball 'in P(Ξ) centered at the nominal distribution P̂N', so the centre is a distribution supported on Ξ; the empirical nominal (3) is supported on Ξ because its samples are, and §2.3 uses elliptical nominals only with Ξ = R^m. Without it (10) fails (Ξ = (−∞, 0], P̂N = δ_1, p = 1, ε = 1/2, ℓ(ξ) = ξ², the ball is empty so the left side is −∞, while ℓ_γ(1) = +∞ for every γ ≥ 0 so the right side is +∞)
--   - encoding: R^m with an arbitrary norm ‖·‖ → a finite-dimensional real normed space E with its Borel σ-algebra; reason: the same instances up to linear isometry
--   - encoding: P(Ξ), the probability distributions supported on Ξ → Borel probability measures Q with Q Ξᶜ = 0; reason: same objects for closed Ξ
--   - encoding: E^Q[ℓ(ξ)] = ∞ when both parts are infinite (p. 2); sup and inf of extended real values → the definition risk; ⨆ and ⨅ in EReal; reason: the paper's convention written out; the complete lattice [−∞, ∞] has no junk values
--   - encoding: Assumption 1 (p. 9, tacitly assumed throughout) and the measurable loss of p. 1 → hypotheses husc : UpperSemicontinuous ℓ and hint : ∫⁻ |ℓ| dP < ⊤; no separate measurability hypothesis; reason: the paper's standing assumptions made explicit; upper semicontinuity implies Borel measurability
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.1, unnumbered sentence after Theorem 7, p. 10

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_worstCaseRisk
import Definitions.Def_WassersteinDRO_StrongDuality_moreauYosida

open MeasureTheory

namespace WassersteinDRO.StrongDuality

/-- **The right-hand side of (10) is the Lagrangian dual of the worst-case risk problem (6).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.1, unnumbered sentence after Theorem 7, p. 10: "The minimization problem on the right hand
side of (10) can indeed be identified with the strong Lagrangian dual of problem (6), where γ ≥ 0 is
the Lagrange multiplier of the Wasserstein constraint Wp(Q, P̂N) ≤ ε."

Let `p ≥ 1`, `Ξ` closed, `P` a Borel probability measure with `P(Ξᶜ) = 0`, `ℓ : E → [−∞, ∞]` upper
semicontinuous with `∫ |ℓ| dP < ∞` (Assumption 1, p. 9), and `ε ≥ 0`. For every multiplier
`γ ≥ 0`:

(a) (dual function) the supremum over `Q ∈ P(Ξ)` with `W_p(Q, P) < ∞` of the Lagrangian
`R(Q, ℓ) − γ (W_p(Q, P)^p − ε^p)` equals `E^P[ℓ_γ(ξ)] + γ ε^p`, the objective of (10) at `γ`;

(b) (weak duality) `R_{ε,p}(P, ℓ) ≤ E^P[ℓ_γ(ξ)] + γ ε^p`.

**Formalization Note.** The constraint is dualized in the form `W_p^p ≤ ε^p`, which the term
`γ ε^p` of (10) fixes. The supremum in (a) runs over `Q` with finite `W_p(Q, P)`, so the subtracted
term is a real number; measures with `W_p = ∞` give the Lagrangian the value `−∞` when `γ > 0`,
and when `γ = 0` they give at most `sup_Ξ ℓ`, which the finite-distance measures already reach,
so the restriction changes no value. The expectations use the paper's convention (`risk`). "Strong"
duality, the equality of the primal value with the dual infimum, is Theorem 7 itself.
Measurability of `ℓ` (p. 1) is implied by upper semicontinuity and is not a separate hypothesis. -/
theorem lagrangian_dual_function {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) {Ξ : Set E} (hΞ : IsClosed Ξ)
    (P : Measure E) [IsProbabilityMeasure P] (hPΞ : P Ξᶜ = 0)
    (ℓ : E → EReal) (husc : UpperSemicontinuous ℓ) (hint : ∫⁻ ξ, EReal.abs (ℓ ξ) ∂P < ⊤)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ γ : ℝ, 0 ≤ γ →
      (⨆ Q ∈ {Q : Measure E | IsProbabilityMeasure Q ∧ Q Ξᶜ = 0 ∧ wasserstein p Q P < ⊤},
          risk Q ℓ - ((γ * ((wasserstein p Q P).toReal ^ p - ε ^ p) : ℝ) : EReal))
        = risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal)) ∧
    (∀ γ : ℝ, 0 ≤ γ →
      worstCaseRisk ε p P Ξ ℓ ≤ risk P (moreauYosida ℓ Ξ γ p) + ((γ * ε ^ p : ℝ) : EReal)) := by sorry

end WassersteinDRO.StrongDuality
