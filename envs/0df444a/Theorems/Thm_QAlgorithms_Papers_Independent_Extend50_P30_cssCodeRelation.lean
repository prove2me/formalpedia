-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_cssCodeRelation
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.cssCodeRelation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:15:39.104877+00:00
-- url     : https://prove2.me/theorems/95519c08-90dc-4031-9a94-84c95de7a724
-- title:
--   CSS code operators and the projection converse
-- statement:
--   For prime $d$, $t\geq1$, and any defect subspace $N$, let $T_N=\{(x,y):x,y\in N^\perp,\ x-y\in N\}$ and let $P_{\rm CSS(N)}$ be the independent Pauli average over $Z^pX^q$, $p,q\in N$. The forward statement is proportionality. Conversely, if $T\in\Sigma_{t,t}(d)$ has unscaled $r(T)$ an orthogonal projection, $T$ is the CSS relation for its left defect.
--
--   $$
--   r(T_N)=|N|P_{\rm CSS(N)}=d^{\dim N}P_{\rm CSS(N)}.
--   $$
--
--   This gives the source's css code operators and the projection converse in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 40, theorem-4.24

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.40, Theorem 4.24: forward proportionality and only the printed projection converse. -/
theorem cssCodeRelation (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    (∀ N : Submodule (ZMod d) (ResidueRegister d t), IsDefect N →
      relationOperator (cssRelation N) = (Nat.card N : ℂ) • cssProjector N ∧
      relationOperator (cssRelation N) = ((d : ℂ) ^ Module.finrank (ZMod d) N) • cssProjector N) ∧
    (∀ T : Lagrangian d t, (relationOperator T.val).IsHermitian →
      relationOperator T.val * relationOperator T.val = relationOperator T.val →
      T.val = cssRelation (leftDefect T.val)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
