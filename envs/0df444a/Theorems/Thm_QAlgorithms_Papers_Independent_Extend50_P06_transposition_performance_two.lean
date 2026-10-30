-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_transposition_performance_two
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.transposition_performance_two
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:46:44.488559+00:00
-- url     : https://prove2.me/theorems/481ef5db-e851-4daa-9ad8-081df7bc4816
-- title:
--   E.4 / Eq.(122): transposition k=2
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   On three ordered factors put $X=I_1\otimes J(I)_{23}$, $V=F_{12}\otimes I_3$, $A_\pm=(I\pm V)/2$, and $q=d^2-1$. Define
--   $$\begin{aligned}S_\pm&=A_\pm(I-2X/(d\pm1))A_\pm,\\S_0&=[d(X+VXV)-(XV+VX)]/q,\\S_1&=[d(XV+VX)-(X+VXV)]/q,\\S_2&=(X-VXV)/\sqrt q,\qquad S_3=i(XV-VX)/\sqrt q.\end{aligned}$$ For $d\ge2$, at $k=2$ the transposition performance operator is
--   $$\Omega=\frac1{d^2}\sum_{a\in\{+,-,0,1,2,3\}:\,S_a\ne0}\frac{\epsilon_a(S_a)_{OP}\otimes(S_a)_{IF}}{\operatorname{tr}(S_a^\dagger S_a)},\qquad \epsilon_3=-1,\quad\epsilon_a=1\ (a\ne3).$$
--   Zero members are omitted, in particular the minus projector at $d=2$. Projector denominators equal their traces; other denominators equal the printed squared-operator traces. The imaginary member causes the minus sign. This retains exact physical wire order and gives the explicit objective.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 34, E.4 / Eq.(122): transposition k=2

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

/-- PDF p.34, Eq.(122): explicit mixed S basis, with crossed placement,
zero S- omitted at d=2, and the imaginary S3 sign retained. -/
theorem transposition_performance_two (d : ℕ) (hd : 2 ≤ d) (H : HaarLaw d) :
    performance (k := 2) H transposeTarget = sixExpansion d true (sBasis d) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
