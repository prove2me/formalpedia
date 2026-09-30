-- Prove2me | Theorems.Thm_RobustLP_Counterpart_alpha_beta_ratio
-- name    : RobustLP.Counterpart.alpha_beta_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:29:58.136252+00:00
-- url     : https://prove2.me/theorems/0b4c0485-ddec-4242-9f61-a2de121f3774
-- title:
--   The ratio $\alpha_i(x)/\beta_i(x)$ is at most $\sqrt{\mathrm{card}(J_i)}/\Omega$, and this is attained (corrected)
-- statement:
--   Let $A=(a_{ij})$ be the inequality matrix of an uncertain linear program, $J_i$ the uncertain-entry set of row $i$, and $\Omega>0$. For $x\in\mathbb{R}^n$ put
--   $$
--   \alpha_i(x)=\sum_{j\in J_i}|a_{ij}||x_j|,\qquad \beta_i(x)=\Omega\sqrt{\sum_{j\in J_i}a_{ij}^2x_j^2}.
--   $$
--   Then
--
--   1. for every $x$, $\ \Omega\,\alpha_i(x) \le \sqrt{\mathrm{card}(J_i)}\ \beta_i(x)$;
--   2. if $J_i\neq\emptyset$ and $a_{ij}\neq0$ for all $j\in J_i$, there is $x$ with $\beta_i(x)>0$ and $\Omega\,\alpha_i(x) = \sqrt{\mathrm{card}(J_i)}\ \beta_i(x)$.
--
--   Hence the largest value of $\alpha_i(x)/\beta_i(x)$ over $x$ with $\beta_i(x)>0$ is $\sqrt{\mathrm{card}(J_i)}/\Omega$. This quantifies by how much the (IRC) constraint can exceed the (RC) one.
--
--   **Formalization Note** Corrected statement. The page says "the ratio $\alpha_i(x)/\beta_i(x)$ can be as large as $\sqrt{\mathrm{card}(J_i)}$", but its $\beta_i$ contains the factor $\Omega$, so the supremum of the printed ratio is $\sqrt{\mathrm{card}(J_i)}/\Omega$; the printed value is that of $\alpha_i(x)\big/\sqrt{\sum_{j\in J_i}a_{ij}^2x_j^2}$. The statement is multiplied out to avoid division.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 420, §3.1, 'Now, the ratio α_i(x)/β_i(x) can be as large as √card(J_i)' (corrected by the factor Ω)

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP

namespace RobustLP.Counterpart

/-- **The ratio `α_i/β_i`** (Ben-Tal–Nemirovski 2000, §3.1, p. 420), corrected for the factor `Ω`.
With `α_i(x) = ∑_{j ∈ J_i} |a_{ij}| |x_j|` and `β_i(x) = Ω √(∑_{j ∈ J_i} a_{ij}² x_j²)`, `Ω > 0`:
(a) `Ω α_i(x) ≤ √card(J_i) · β_i(x)` for every `x`, and
(b) if `J_i` is nonempty and `a_{ij} ≠ 0` for every `j ∈ J_i`, some `x` has `β_i(x) > 0` and
`Ω α_i(x) = √card(J_i) · β_i(x)`.
So the largest value of `α_i/β_i` is `√card(J_i)/Ω` (the page prints `√card(J_i)`). -/
theorem alpha_beta_ratio {n p m : ℕ} (L : UncertainLP n p m) (Ω : ℝ) (hΩ : 0 < Ω)
    (i : Fin m) :
    (∀ x : Fin n → ℝ,
      Ω * ∑ j ∈ L.J i, |L.A i j| * |x j| ≤
        Real.sqrt ((L.J i).card) * (Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2))) ∧
    ((L.J i).Nonempty → (∀ j ∈ L.J i, L.A i j ≠ 0) →
      ∃ x : Fin n → ℝ, 0 < Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2) ∧
        Ω * ∑ j ∈ L.J i, |L.A i j| * |x j| =
          Real.sqrt ((L.J i).card) * (Ω * Real.sqrt (∑ j ∈ L.J i, L.A i j ^ 2 * x j ^ 2))) := by sorry

end RobustLP.Counterpart
