-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_inversion_performance_two
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.inversion_performance_two
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:48:11.013492+00:00
-- url     : https://prove2.me/theorems/c0eaa6fc-6af9-49d3-98c5-eef8c1f40119
-- title:
--   E.5 / Eq.(125): inversion k=2
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   On three ordered factors, let $V_{12},V_{23},V_{31}$ be swaps and $V_{123},V_{321}$ the indicated cyclic permutation matrices. Define
--   $$\begin{aligned}R_+&=(I+V_{12}+V_{23}+V_{31}+V_{123}+V_{321})/6,\\R_-&=(I-V_{12}-V_{23}-V_{31}+V_{123}+V_{321})/6,\\R_0&=(2I-V_{123}-V_{321})/3,\\R_1&=(2V_{23}-V_{31}-V_{12})/3,\\R_2&=(V_{12}-V_{31})/\sqrt3,\qquad R_3=i(V_{123}-V_{321})/\sqrt3.\end{aligned}$$ For $d\ge2$, at $k=2$ the inversion performance operator is
--   $$\Omega=\frac1{d^2}\sum_{a\in\{+,-,0,1,2,3\}:\,R_a\ne0}\frac{\epsilon_a(R_a)_{OP}\otimes(R_a)_{IF}}{\operatorname{tr}(R_a^\dagger R_a)},\qquad \epsilon_3=-1,\quad\epsilon_a=1\ (a\ne3).$$
--   Zero members are omitted, in particular the minus projector at $d=2$. Projector denominators equal their traces; other denominators equal the printed squared-operator traces. The imaginary member causes the minus sign. This retains exact physical wire order and gives the explicit objective.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 34, E.5 / Eq.(125): inversion k=2

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

/-- PDF p.34, Eq.(125): printed “trans” changed to inversion by Eq.(123);
R- is omitted at d=2 and the imaginary R3 term has minus sign. -/
theorem inversion_performance_two (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    performance (k := 2) H inverseTarget = sixExpansion d true (rBasis d) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
