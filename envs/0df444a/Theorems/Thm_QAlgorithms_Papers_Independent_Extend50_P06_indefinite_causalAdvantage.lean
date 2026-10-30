-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_indefinite_causalAdvantage
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.indefinite_causalAdvantage
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:42:50.975407+00:00
-- url     : https://prove2.me/theorems/2fbbee4d-7c28-4b89-ae3b-99008b877f0f
-- title:
--   §6.1: strict general-versus-sequential advantage
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   There is strict advantage of the general domain over sequential processes in precisely these five claimed instances:
--   $$F_{\rm gen}^*(f;d,k)>F_{\rm seq}^*(f;d,k),\qquad(f,d,k)\in\{(U^T,2,2),(U^T,2,3),(U^{-1},2,2),(U^{-1},2,3),(U^T,3,2)\}.$$
--   Both optima in every comparison are attained. The two-query comparisons have reported certification; the three-query comparisons are based on the source's numerical evidence. The mathematical general-process domain does not assert fair physical realization of every element.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 23, §6.1: strict general-versus-sequential advantage

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P06

namespace QAlgorithms.Papers.Independent.Extend50.P06

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

-- Exact accepted interfaces; no duplicate SU subtype or ambient-coordinate Haar law.

open QAlgorithms.Papers.Independent.Information100.P47 (Mat)

open QAlgorithms.Papers.Independent.Claimed50.P21 (SU HaarLaw)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P06.targetMatrixMeasurable

/-- PDF pp.23–24, §6.1: exactly five strict general/sequential comparisons.
k=2 is reported computer certified; k=3 rests on the paper's numerical evidence.
“General” is Definition 4, not a claim of fair physical realization. -/
theorem indefinite_causalAdvantage (H2 : HaarLaw 2) (H3 : HaarLaw 3) :
    StrictAdvantage (k := 2) H2 transposeTarget ∧
    StrictAdvantage (k := 3) H2 transposeTarget ∧
    StrictAdvantage (k := 2) H2 inverseTarget ∧
    StrictAdvantage (k := 3) H2 inverseTarget ∧
    StrictAdvantage (k := 2) H3 transposeTarget := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
