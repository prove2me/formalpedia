-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P03_projection_sandwich_trace_bound
-- name    : QAlgorithms.Papers.Independent.Frontier18.P03.projection_sandwich_trace_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:32:02.048993+00:00
-- url     : https://prove2.me/theorems/443b570d-8da5-4514-a92e-3876b26a5822
-- title:
--   Projection sandwich trace bound
-- statement:
--   Let $\rho$ be any positive trace-class operator of trace one on a complex Hilbert space. Let $
--   u$ and $\tau$ be orthogonal projections, with $\rho
--   u=
--   u\rho$. Then $$\operatorname{Tr}(\rho\tau
--   u\tau)\ge\operatorname{Tr}(\rho
--   u)-2\operatorname{Tr}(\rho(I-\tau)).$$ The two projections need not commute, and $\rho$ may have infinite rank.
--
--   This bound estimates the loss from placing a projection test between two copies of another projection.
--
--   **Formalization Note** A state is presented as $\rho=\sum_j|v_j\rangle\langle v_j|$ with $\sum_j\|v_j\|^2=1$. Every density operator has such a presentation, even on a nonseparable ambient Hilbert space. All trace series against bounded operators converge absolutely.
-- source:
--   General formulas for capacity of classical-quantum channels, arXiv:quant-ph/0206186v4, PDF p. 23, Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P03

noncomputable section

open Filter

namespace QAlgorithms.Papers.Independent.Frontier18.P03

/-- Lemma 6, PDF p.23. Only rho and nu commute; nu and tau need not
commute. The state representation includes every infinite-rank density
operator. The bounded operators act on the entire Hilbert space. -/
theorem projection_sandwich_trace_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (rho : DensityPresentation H) (nu tau : H →L[ℂ] H)
    (hnu : IsOrthogonalProjection nu) (htau : IsOrthogonalProjection tau)
    (hcomm : ∀ v, densityAction rho (nu v) = nu (densityAction rho v)) :
    traceAgainst rho (tau.comp (nu.comp tau)) ≥
      traceAgainst rho nu - 2 * traceAgainst rho (1 - tau) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P03

end
