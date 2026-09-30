-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_time_axis_jet_box_certificate
-- name    : WeierstrassEllipticZeta.time_axis_jet_box_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T22:38:20.859518+00:00
-- url     : https://prove2.me/theorems/b0e46369-31cc-4647-9944-eea6e85a97a6
-- title:
--   Time-axis boxes interpolate all finite contact jets
-- statement:
--   Let V be a finite set of chart points whose time coordinates are distinct, and let N be a natural number. The box with time side bound N|V| and all other side bounds zero contains a nonzero polynomial in every order-N contact ideal, with weighted-face cost at most N|V|. Every polynomial has the same order-N contact jets on V as a polynomial supported in this box.
--
--   The contact polynomial is the product of (X₀ − v₀)^N over v ∈ V. The interpolation assertion follows from the already proved bounded Hermite interpolation theorem. Empty point sets and N = 0 are included.
-- source:
--   Derived time-axis interpolation construction for the frontier https://prove2.me/theorems/1cce73f4-b850-4bca-a245-16357d88ad77. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, especially the time coordinate of the analytic subgroup and the numerical zero estimate Theorem A.3, https://doi.org/10.1017/S001309152610145X. This certificate is a derived construction using the already proved bounded Hermite interpolation theorem (20ad754f-4a6a-45a2-a323-9c692a5f3f83), not a quotation from the article. The remaining numerical alternative is an open sufficient condition for this frontier; no equivalence or completed global zero estimate is claimed. Lean/Mathlib environment: 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_bounded_hermite_interpolation
import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat

open WeierstrassEllipticZeta
open scoped Classical

noncomputable section

theorem WeierstrassEllipticZeta.time_axis_jet_box_certificate
    (G : Frontier.Geometry) (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (N : ℕ)
    (hinj : Function.Injective (fun v : V => v.val 0)) :
    let b : Fin 4 →₀ ℕ := Finsupp.single 0 (N * V.card)
    ∃ p : MvPolynomial (Fin 4) ℂ,
      p ≠ 0 ∧ (∀ i : Fin 4, p.degreeOf i ≤ b i) ∧
      (∑ i : Fin 4, p.degreeOf i *
        ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, (b j + 1)) ≤ N * V.card ∧
      (∀ v : V, p ∈ extensionChartContactIdeal G.L.g₂ G.L.g₃ c v.val N) ∧
      ∀ q : MvPolynomial (Fin 4) ℂ, ∃ r : MvPolynomial (Fin 4) ℂ,
        r.support ⊆ Finset.Iic b ∧
        ∀ (v : V) (k : Fin N), MvPolynomial.eval v.val
          ((extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k.val] (q - r)) = 0 := by sorry
