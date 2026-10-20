-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_correlatedInputEntropy
-- name    : QAlgorithms.Papers.Independent.Information100.P67.correlatedInputEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:59:17.422068+00:00
-- url     : https://prove2.me/theorems/c15bc68f-13a2-4038-a24a-8e436db078cc
-- title:
--   Unnumbered Appendix B.2 result: uniform correlated-input entropy bound (B.22)/(6.14)
-- statement:
--   Let $T:A\to FE'$ be any fixed CPTP map on finite nonempty systems, let $n\ge1$, and let $0<u<1$. Put $g_n=(n+1)^{(\dim A)^2}$ and $v=u^2/(32g_n)$. The set of values $H_{\max}^{v}(F^n|E'^{n})_{T(\sigma)^{\otimes n}}$, as $\sigma$ ranges over normalized input density matrices, is nonempty and bounded above. For every normalized, possibly correlated input $\rho_{A^n}$,
--
--   $$H_{\max}^{u}(F^n|E'^{n})_{T^{\otimes n}(\rho)}\le\sup_{\sigma\in\mathcal S(A)}H_{\max}^{v}(F^n|E'^{n})_{T(\sigma)^{\otimes n}}+3\log_2g_n+5+2\log_2(1/u).$$
--
--   All smooth entropies use subnormalized purified-distance balls about normalized centers. The numerical estimate is uniform over $\rho$ and keeps the stronger $+5$ version of (B.22); the $+6$ version follows immediately. The supremum states an upper bound without adding an attainment claim.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 30, Unnumbered Appendix B.2 result: uniform correlated-input entropy bound (B.22)/(6.14)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Uniform correlated-input bound (B.22), PDF p.45, with the stronger +5.
T is ANY fixed CPTP map, not necessarily a degradable factorization. -/
theorem correlatedInputEntropy [Nonempty A] [Nonempty B] [Nonempty E]
    (Tmap : Superop A (B × E)) (hT : IsChannel Tmap)
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    let g := postselectionFactor (Fintype.card A) n
    let v := u ^ 2 / (32 * g)
    let values := {h | ∃ sigma : Matrix A A ℂ, IsDensityMatrix sigma ∧
      h = smoothConditionalMaxEntropy (groupedPower (Tmap sigma) n) v}
    values.Nonempty ∧ BddAbove values ∧
    ∀ rho : Matrix (Fin n → A) (Fin n → A) ℂ, IsDensityMatrix rho →
      smoothConditionalMaxEntropy (groupedChannelPower Tmap n rho) u ≤
        sSup values + 3 * Real.logb 2 g + 5 + 2 * Real.logb 2 (1 / u) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
