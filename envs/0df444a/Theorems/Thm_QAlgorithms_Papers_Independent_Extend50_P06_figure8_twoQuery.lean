-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P06_figure8_twoQuery
-- name    : QAlgorithms.Papers.Independent.Extend50.P06.figure8_twoQuery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:41:58.892571+00:00
-- url     : https://prove2.me/theorems/4ac2ea7b-94fd-4587-85f4-07e5eb23b15b
-- title:
--   §6 / Figure 8: certified two-query values
-- statement:
--   All registers have specified computational bases and positive finite dimensions. An unknown operation is the channel of $U\in\mathrm{SU}(d)$, with $k\ge1$ identical black-box uses. Every process, probe, measurement and guess is fixed independently of $U$. The unnormalized input-first Choi operator is $J(V)=|V\rangle\!\rangle\langle\!\langle V|$, where $|V\rangle\!\rangle=\sum_i|i\rangle\otimes V|i\rangle$. For a target $f(U)$ of dimension $e$, write $F(S,f;U)=\operatorname{Re}\operatorname{tr}[(S*J(U)^{\otimes k})J(f(U))]/e^2$ and $\overline F(S,f)=\int F(S,f;U)\,dU$, for probability Haar measure. Parallel, sequential and general processes mean Definitions 2–4, with arbitrary finite memory. Write $F_c^*(f;d,k)$ for the greatest attained average fidelity in class $c$; any displayed optimum includes attainment.
--
--   At $k=2$, every listed optimal average fidelity is attained and differs from the displayed decimal by at most $10^{-4}$:
--   $$\begin{array}{c|c|ccc}f&d&\mathrm{parallel}&\mathrm{sequential}&\mathrm{general}\\\hline U^T&2&.6545&.7500&.8249\\U^T&3&.3333&.4074&.4349\\U^{-1}&2&.6545&.7500&.8249\\U^{-1}&3&.3333&.3333&.3333\end{array}$$
--   These are the paper's reported computer-assisted certifications. Rounded decimals are not exact equalities and no three-query decimal is asserted certified.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, PDF p. 23, §6 / Figure 8: certified two-query values

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

/-- Figure 8 and caption, PDF p.23: all twelve k=2 entries, with absolute
error ≤10^{-4}. No k=3 decimal is asserted certified. -/
theorem figure8_twoQuery (H2 : HaarLaw 2) (H3 : HaarLaw 3) :
    Certified (k := 2) H2 transposeTarget .parallel (6545/10000) ∧
    Certified (k := 2) H2 transposeTarget .sequential (7500/10000) ∧
    Certified (k := 2) H2 transposeTarget .general (8249/10000) ∧
    Certified (k := 2) H3 transposeTarget .parallel (3333/10000) ∧
    Certified (k := 2) H3 transposeTarget .sequential (4074/10000) ∧
    Certified (k := 2) H3 transposeTarget .general (4349/10000) ∧
    Certified (k := 2) H2 inverseTarget .parallel (6545/10000) ∧
    Certified (k := 2) H2 inverseTarget .sequential (7500/10000) ∧
    Certified (k := 2) H2 inverseTarget .general (8249/10000) ∧
    Certified (k := 2) H3 inverseTarget .parallel (3333/10000) ∧
    Certified (k := 2) H3 inverseTarget .sequential (3333/10000) ∧
    Certified (k := 2) H3 inverseTarget .general (3333/10000) := by sorry

end

end QAlgorithms.Papers.Independent.Extend50.P06
