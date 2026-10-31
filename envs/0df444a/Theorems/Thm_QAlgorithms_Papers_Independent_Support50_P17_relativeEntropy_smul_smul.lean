-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropy_smul_smul
-- name    : QAlgorithms.Papers.Independent.Support50.P17.relativeEntropy_smul_smul
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-29T18:22:09.458747+00:00
-- url     : https://prove2.me/theorems/16117123-d942-4ef2-9278-1517d1b96dfc
-- title:
--   Relative entropy of two multiples of the same positive operator
-- statement:
--   Let $X\ge0$ be a positive semidefinite operator on a finite-dimensional complex Hilbert space and let $a\ge0$, $b>0$ be real numbers. Then the unnormalised Umegaki relative entropy satisfies
--
--   $$
--   D(aX\|bX)=a\log\frac ab\,\operatorname{Tr}X ,
--   $$
--
--   with the convention $0\log0=0$ (so both sides vanish when $a=0$). In particular $D(X\|X)=0$. These are the elementary values that appear after splitting a pair of operators into commuting pieces.
--
--   **Formalization Note** `relativeEntropy` is the frozen definition of Dependency50.P21; the scalars are real numbers cast to $\mathbb C$, and $\operatorname{Tr}X$ enters through its real part.
-- source:
--   Direct computation from Umegaki's definition (Ohya--Petz, Quantum Entropy and Its Use, Ch. 1); used in Audenaert--Eisert, Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, proof of Corollary 1 (PDF p. 9), pieces (beta +- T) P vs beta P

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

theorem relativeEntropy_smul_smul {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    relativeEntropy ((a : ℂ) • X) ((b : ℂ) • X) =
      ((a * Real.log (a / b) * X.trace.re : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
