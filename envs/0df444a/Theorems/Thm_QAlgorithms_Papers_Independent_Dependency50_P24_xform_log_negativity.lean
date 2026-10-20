-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P24_xform_log_negativity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P24.xform_log_negativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:12:30.349765+00:00
-- url     : https://prove2.me/theorems/b03228e4-8da6-4753-a3e0-dc66d20ad231
-- title:
--   Lemma 3: logarithmic negativity
-- statement:
--   All spaces are finite dimensional and have positive dimension. A state means a positive semidefinite operator of trace one. The distinguished product basis $B$ is fixed and is used for both twisting and key measurement. Norms are full trace norms, fidelity $F$ is root fidelity, and logarithms are in bits.
--
--   Let $X$ be a shield operator with $\|X\|_1=1$ and let $\gamma_X$ be its private bit in X-form, with diagonal blocks $\sqrt{XX^\dagger}/2$ and $\sqrt{X^\dagger X}/2$ and corner $X/2$. Suppose both square-root diagonal operators have positive partial transpose on $B'$. Then
--
--   $$E_N(\gamma_X)=\log_2\bigl(1+\|X^{\Gamma_{B'}}\|_1\bigr),\qquad E_N(\rho)=\log_2\|\rho^{\Gamma_{BB'}}\|_1.$$
--
--   This evaluates the logarithmic negativity in terms of one shield operator.
-- source:
--   General paradigm for distilling classical key from quantum states, arXiv:quant-ph/0506189v2, PDF p. 11, Lemma 3: logarithmic negativity

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF p.11, Lemma 3; pp.37–38, Eqs.(260)–(265): PPT is on the SQUARE ROOT
blocks. The omitted roots in intermediate Eq.(263) are a typo. -/
theorem xform_log_negativity {S T : Type*} [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T] (X : Op (S × T)) (hX : traceNorm X = 1)
    (hleft : (transposeSecond (cfc Real.sqrt (X*Xᴴ))).PosSemidef)
    (hright : (transposeSecond (cfc Real.sqrt (Xᴴ*X))).PosSemidef) :
    logNegativity (xForm X) = logBits (1 + traceNorm (transposeSecond X)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P24

end
