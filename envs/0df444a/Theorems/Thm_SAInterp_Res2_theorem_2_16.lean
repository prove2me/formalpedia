-- Prove2me | Theorems.Thm_SAInterp_Res2_theorem_2_16
-- name    : SAInterp.Res2.theorem_2_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:38:37.266553+00:00
-- url     : https://prove2.me/theorems/2aa6fa1d-2b29-482a-886a-02432dc2cf99
-- title:
--   Theorem 2.16 — the booleanization of a degree-d indicator design is a degree-d design agreeing on indicator conjunctions; pseudoexpectations stay pseudoexpectations
-- statement:
--   Let $X=\{(x_v,S_v)\}$ be a finite collection of multivalued variables with $|S_v|=2^{w_v}$, and let $D:A(X)_{\le d}\to\mathbb R$ be a degree-$d$ indicator design. Then the booleanization $D^{\mathrm{bool}}$ (Definition 2.15) is a degree-$d$ design on $\mathbb R[x,\bar x]$ over the bits of $X$ (Definition 2.4), and
--   $$D[C]=D^{\mathrm{bool}}[C^{\mathrm{bool}}]\qquad\text{for every indicator conjunction }C\text{ with }\mathrm{bdeg}(C)\le d.$$
--   Moreover, if $D$ is an indicator pseudoexpectation, then $D^{\mathrm{bool}}$ is a pseudoexpectation.
--
--   This transfer principle turns the block-degree pseudoexpectation of the multivalued $\mathrm{CPLS}_n$ into a pseudoexpectation of its binary encoding.
--
--   Differences from the source:
--   - encoding: S_v = {a_{v,0}, …, a_{v,2^{w_v}−1}} with x_v = a_{v,j} iff Σ_k 2^k x_{v,k} = j → `Fin (size v)` with `size v = 2 ^ w v`, bit k of value j is `j.testBit k`; reason: Lean convention, same encoding.
--   - encoding: D^bool defined on conjunctions and extended by linearity and modulo the boolean/complementarity ideal → defined on every monomial by reading x_b^e, x̄_b^e (e ≥ 1) as x_b, x̄_b, extended linearly; reason: picks the representative the ideal prescribes; agrees with the paper's D^bool wherever that is defined.
--   - encoding: an indicator design on A(X)_{≤d} → a function on A(X) constrained only on A(X)_{≤d}; reason: Lean convention, same designs.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 21 (PDF p. 23), Theorem 2.16

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_SAInterp_Res2_SherAdams
import Definitions.Def_SAInterp_Res2_Indicator

open MultiplierAssoc206.Resolution

namespace SAInterp.Res2

/-- Theorem 2.16 (p. 21): for multivalued variables with `|S_v| = 2^{w_v}`, the booleanization
`D^bool` of a degree-`d` indicator design `D` is a degree-`d` design with
`D[C] = D^bool[C^bool]` for every indicator conjunction `C` with `bdeg(C) ≤ d`; if `D` is an
indicator pseudoexpectation, `D^bool` is a pseudoexpectation. -/
theorem theorem_2_16 {V : Type} [Fintype V] (size w : V → ℕ) (hw : ∀ v, size v = 2 ^ w v)
    (d : ℕ) (D : IndAlg size → ℝ) (hD : IsIndicatorDesign d D) :
    IsDesign d (booleanization w D) ∧
    (∀ C : IndConj size, bdeg C ≤ d →
      D (indConj C) = booleanization w D (conjPoly (conjBool w C))) ∧
    (IsIndPseudoexpectation d D → IsPseudoexpectation d (booleanization w D)) := by sorry

end SAInterp.Res2
