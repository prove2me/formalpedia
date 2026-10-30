-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_forgetting_herald
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.forgetting_herald
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:36:51.263507+00:00
-- url     : https://prove2.me/theorems/50004cf1-04ce-438b-8cc3-bb519ff33541
-- title:
--   §3.1.4 / Eq.(23): forgetting heralding
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   Let $f:\mathrm{SU}(d)\to\mathrm{SU}(e)$ be Borel-measurable. Let $S_s,S_f$ be positive semidefinite branches whose sum is a deterministic process in a specified class. Suppose a fixed $p_s\in[0,1]$ satisfies $S_s*J(U)^{\otimes k}=p_sJ(f(U))$ for every $U$. Then the explicitly constructed process $S=S_s+S_f$ lies in that class and satisfies
--   $$\overline F(S,f)=p_s+\int\frac{\operatorname{Re}\operatorname{tr}[(S_f*J(U)^{\otimes k})J(f(U))]}{e^2}\,dU\ge p_s.$$
--   Forgetting the herald produces a deterministic approximation; the source's phrase deterministic exact is a typo.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 13, §3.1.4 / Eq.(23): forgetting heralding

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

/-- PDF p.13, Eq.(23): forgetting the herald gives S=Ss+Sf. Printed
“deterministic exact” is changed to deterministic non-exact, consistent with
the section heading and the displayed inequality; only Ss is exact. -/
theorem forgetting_herald (d e k : ℕ) (hd : 0 < d) (he : 0 < e) (hk : 1 ≤ k)
    (H : HaarLaw d) (f : Target d e) (c : StrategyClass)
    (Ss Sf : TransformationProcess k d e) (ps : ℝ) (hps : 0 ≤ ps ∧ ps ≤ 1)
    (hs : Ss.PosSemidef) (hf : Sf.PosSemidef) (hdet : TransformationAdmissible c (Ss+Sf))
    (hexact : ∀ U : SU d, insertSlots Ss (unitarySlots U.val) = (ps : ℂ) • transformationChoi (f.value U)) :
    TransformationAdmissible c (Ss+Sf) ∧
      transformationAverage H f.value (Ss+Sf) = ps +
        (∫ U, pointFidelity Sf f.value U ∂H.law) ∧
      ps ≤ transformationAverage H f.value (Ss+Sf) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
