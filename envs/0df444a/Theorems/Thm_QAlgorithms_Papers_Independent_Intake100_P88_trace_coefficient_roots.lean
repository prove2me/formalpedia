-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_trace_coefficient_roots
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.trace_coefficient_roots
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:38:53.270929+00:00
-- url     : https://prove2.me/theorems/f4409896-fe10-4631-a020-dcefe606eb63
-- title:
--   Unnumbered (3.26): zeros of trace coefficients
-- statement:
--   For a Young diagram $\mu$ of size $r$, with hook lengths $h(b)$ and row lengths padded by zeros, set
--
--   $$t_\mu(z)=\left(\prod_{b\in\mu}h(b)^{-1}\right)\prod_{j=1}^{r}(z-r-\mu_j+j),\qquad
--   u_\mu(z)=z\,t_\mu(z-1).$$
--
--   Their degrees are $r$ and $r+1$. At doubled level $m$, use $t_\mu$ for even $m$ and $u_\mu$ for odd $m$, over labels $r\le\lfloor m/2\rfloor$. The union $R_m$ of their complex zero sets is
--
--   $$R_1=\{0\},\quad R_2=\{1\},\quad R_3=\{0,2\},\quad R_m=\{0,1,\ldots,m-1\}\ (m\ge4).$$
--
--   The symbol $u_\mu$ denotes the half-level polynomial above. Empty products are one. The formula describes unions over labels, and identifies the parameter values relevant to the trace criterion.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 24, Unnumbered (3.26): zeros of trace coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Degrees and complete unions of roots, PDF p.24, equation (3.26).
The level-one coefficient is the integer coefficient (subscript read from the PDF). -/
theorem trace_coefficient_roots :
    (∀ mu : YoungDiagram, (traceCoefficient mu).natDegree = mu.card ∧
      (halfTraceCoefficient mu).natDegree = mu.card + 1) ∧
    coefficientRoots 1 = {0} ∧ coefficientRoots 2 = {1} ∧ coefficientRoots 3 = {0, 2} ∧
    (∀ m : ℕ, 4 ≤ m → coefficientRoots m = {z | ∃ j : Fin m, z = (j.val : ℂ)}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
