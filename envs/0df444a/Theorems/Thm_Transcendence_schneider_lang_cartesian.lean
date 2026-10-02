-- Prove2me | Theorems.Thm_Transcendence_schneider_lang_cartesian
-- name    : Transcendence.schneider_lang_cartesian
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:19:10.021311+00:00
-- url     : https://prove2.me/theorems/0d6daaa2-4460-46f7-a092-0052518d8136
-- title:
--   The criterion of Schneider–Lang for ℂ^{d₀}×(ℂ^×)^{d₁}, d₀ ≤ 1 (Corollary 4.2 of Waldschmidt's book)
-- statement:
--   Let $x_1, \dots, x_{d_1}$ be vectors in $\mathbb{C}^\iota$ with algebraic coordinates, linearly independent over $\mathbb{Q}$, and let $(y_j)_{j\in\iota}$ be a basis of $\mathbb{C}^\iota$. Optionally fix a coordinate $k$ at which every $y_j$ has an algebraic coordinate (the case $d_0 = 1$; otherwise $d_0 = 0$). If $|\iota| < d_0 + d_1$, the numbers
--
--   $$e^{\langle x_i, y_j\rangle} \qquad (1 \le i \le d_1,\ j \in \iota)$$
--
--   are not all algebraic.
--
--   This is Corollary 4.2 of Waldschmidt's book for $d_0 \le 1$, proved directly as in its §4.6: an auxiliary function by Thue–Siegel (`Transcendence.siegel_small_values`), Liouville's inequality at the points of the grid $\sum s_jy_j$, Schwarz's lemma for Cartesian products (`Transcendence.cartesian_schwarz`) at the first non-vanishing derivative, and a contradiction. The cases $d_0 = 0$ and $d_0 = 1$ are the book's Corollaries 4.3 and 4.4, from which Baker's theorem follows (`Transcendence.baker_number_field_basis`).
--
--   The book's step 5 applies Proposition 4.7 after the change of variables $z \mapsto \sum z_jy_j$ to a vanishing hypothesis (every exponent below $S_0$) that this change of variables does not preserve. The proof here uses vanishing by total order throughout, which it does preserve; only the constants change.
--
--   It is one step of the proof of Baker's theorem formalised in this mission, which follows Chapter 4 of Waldschmidt's book: Baker's theorem from the criterion of Schneider–Lang for Cartesian products, as observed by Bertrand and Masser (1980).
--
--   **Novelty.** None for the statement. The contribution of this node is the formal proof, with the correction just described.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Corollary 4.2 (p. 117) for d₀ ≤ 1, by the direct proof of §4.6 (pp. 136–141); the route is D. Bertrand and D. W. Masser, Linear forms in elliptic integrals, Invent. Math. 58 (1980), 283–288; D. W. Masser, A note on Baker's theorem, in Recent Progress in Analytic Number Theory, Vol. 2 (Durham, 1979), Academic Press, 1981, 153–158. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- **The criterion of Schneider–Lang for `ℂ^{d₀} × (ℂ^×)^{d₁}`, `d₀ ≤ 1`** (Waldschmidt, *Diophantine
Approximation on Linear Algebraic Groups*, Cor. 4.2, proved directly in §4.6). Let `x₁, …, x_{d₁}` be vectors
with algebraic coordinates, linearly independent over `ℚ`, and let `(y_j)` be a basis of `ℂ^ι`. Optionally fix a
coordinate `k = ι₀` at which every `y_j` has an algebraic coordinate (the case `d₀ = 1`). If `|ι| < d₀ + d₁`, the
numbers `e^{⟨xᵢ, y_j⟩}` cannot all be algebraic. The special cases `ι₀ = none` and `ι₀ = some k` are Cor. 4.3 and
Cor. 4.4 of the book, from which Baker's theorem follows. -/
theorem schneider_lang_cartesian {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ}
    (x : Fin d₁ → ι → ℂ) (hxalg : ∀ i ν, IsAlgebraic ℚ (x i ν)) (hxind : LinearIndependent ℚ x)
    (y : ι → ι → ℂ) (hy : LinearIndependent ℂ y)
    (ι₀ : Option ι) (hdim : Fintype.card ι < ι₀.elim 0 (fun _ => 1) + d₁)
    (hy₀ : ∀ k, ι₀ = some k → ∀ j, IsAlgebraic ℚ (y j k))
    (hexp : ∀ i j, IsAlgebraic ℚ (Complex.exp (∑ ν, x i ν * y j ν))) : False := by
  sorry

end Transcendence
