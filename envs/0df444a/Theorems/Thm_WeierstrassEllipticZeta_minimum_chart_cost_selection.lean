-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_minimum_chart_cost_selection
-- name    : WeierstrassEllipticZeta.minimum_chart_cost_selection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-22T19:03:43.1688+00:00
-- url     : https://prove2.me/theorems/36eba70f-2dd5-4303-ad5a-dba7c6bcbd9c
-- title:
--   Normalized origin chart and attained minimum chart cost
-- statement:
--   Let L be a period pair, let sigma be entire with $\sigma(0)=0$ and $\sigma'(0)=1$ and logarithmic derivative zeta off the lattice, and let S be its five entire extension coordinates with the specified values off the lattice. Then $S_2(0)=-2$.
--
--   For every polynomial Q, natural N,T and finite X containing zero, the finite set V of valid chart-point pairs over X+X+X is nonempty and has at most $2|X+X+X|$ elements. The minimum E_min of the canonical capped chart cost on V is at least one, is attained by a valid pair, and is at most the cost at chart 1 and z=0.
--
--   For any natural W and real R, there is a valid pair with $W E(c,z)\le R$ if and only if $W E_{\min}\le R$. The minimum is independent of W and R. No homogeneity, high-order vanishing, global nonvanishing of the lift, or geometric upper-bound hypothesis is needed for this selection theorem. It does not bound E_min in terms of the polynomial degrees.
-- source:
--   Derived finite chart minimum for the A.1 frontier https://prove2.me/theorems/62ce1ff0-7017-488f-b92c-d199923e4da4. The normalized sigma lift satisfies S_2(0)=-2, by the identity S_2=-2(sigma prime)^3+3*sigma*sigma prime*sigma double-prime-sigma^2*sigma triple-prime, analytic continuation, and sigma(0)=0, sigma prime(0)=1. The derivative of zeta is the already-Proved dependency https://prove2.me/theorems/9d009034-3d4c-416b-90eb-35a15f91a612. Over the triple sumset the finite valid chart set has at most 2*|X+X+X| elements, is nonempty when 0 is in X, and the positive natural local cost attains its minimum E_min. For any natural weight W, the existential chart budget is exactly equivalent to W*E_min<=R. Primary pinned source for finite minimum attainment: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Max.lean (Finset.exists_min_image), and finite infimum laws: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Lattice/Fold.lean. Mission context: Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This is a derived selection lemma, not the uniform geometric estimate. The remaining frontier is W_min*E_min<=C*(m+1)*n^2, with the same C, hypotheses and anchor weight. The chosen chart and its cost may change. No effective computation of local lengths or numeric improvement to the global or integer-search bounds is asserted.

import Definitions.Def_WeierstrassEllipticZeta_MinimumChartCost
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set
open scoped Topology Pointwise Classical
open WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.minimum_chart_cost_selection
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    S 2 0 = -2 ∧ ∀ (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (X : Finset ℂ),
      0 ∈ X →
      (validChartPoints S X).Nonempty ∧
      (validChartPoints S X).card ≤ 2 * (X + X + X).card ∧
      1 ≤ minimumChartCost L S Q N T X ∧
      minimumChartCost L S Q N T X ≤ cappedChartCost L S Q N T 1 0 ∧
      (∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
        S (extensionChartDenominator c) z ≠ 0 ∧
        cappedChartCost L S Q N T c z = minimumChartCost L S Q N T X) ∧
      (∀ (W : ℕ) (R : ℝ),
        (∃ (c : Fin 2) (z : ℂ), z ∈ X + X + X ∧
          S (extensionChartDenominator c) z ≠ 0 ∧
          ((W * cappedChartCost L S Q N T c z : ℕ) : ℝ) ≤ R) ↔
        ((W * minimumChartCost L S Q N T X : ℕ) : ℝ) ≤ R) := by sorry
