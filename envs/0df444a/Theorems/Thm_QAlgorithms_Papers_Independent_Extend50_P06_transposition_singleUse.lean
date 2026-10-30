-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_transposition_singleUse
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.transposition_singleUse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:39:16.479586+00:00
-- url     : https://prove2.me/theorems/af9e0692-aa7d-4088-9806-4a4b55ae0e45
-- title:
--   §5.1.1 / Eq.(55): one-query transposition
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   For $d\ge2$ and one query, the parallel, sequential and general transposition optima coincide and are attained:
--   $$F_c^*(U\mapsto U^T;d,1)=\frac2{d^2}\quad(c\in\{\mathrm{par},\mathrm{seq},\mathrm{gen}\}).$$
--   The restriction excludes the printed formula's impossible value 2 at $d=1$. This applies Theorem 3 to the cited one-use estimation value.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 19, §5.1.1 / Eq.(55): one-query transposition

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

/-- PDF p.19, Eq.(55): one-query transposition, with all three domains.
Printed “any d” needs d≥2: at d=1 the displayed 2/d² equals 2. -/
theorem transposition_singleUse (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    ∀ c : StrategyClass, IsGreatest (scores (k := 1) H transposeTarget c)
      (2/(d : ℝ)^2) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
