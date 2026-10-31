-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P29_residue_iff_jantzen
-- name    : QAlgorithms.Papers.Independent.Intake100.P29.residue_iff_jantzen
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:35:13.421471+00:00
-- url     : https://prove2.me/theorems/930a32c5-6743-47f8-a8d1-88b476139186
-- title:
--   Residue and Jantzen equivalence coincide for all nonzero parameters
-- statement:
--   Let $F$ be a field, $n,r\ge1$, $q\in F^\times\setminus\{1\}$, and let $Q=(Q_1,\ldots,Q_r)\in(F^\times)^r$ be arbitrary. For multipartitions $\lambda,\mu$ of $n$, a node $(i,j,a)$ has field-valued residue $q^{j-i}Q_a$. Let $C_f(\lambda)$ count every node of residue $f\in F$. Let $\sim_J$ be same-size linkage through nonzero coefficients of Definition 2.5. Then
--
--   $$
--   \bigl(\forall f\in F,\ C_f(\lambda)=C_f(\mu)\bigr)
--   \quad\Longleftrightarrow\quad
--   \lambda\sim_J\mu.
--   $$
--
--   This equivalence is uniform over all nonzero parameter tuples; they need not be powers of $q$ or lie in a single $q$-orbit. It is the combinatorial classification used after the paper's orbit reduction.
-- source:
--   Blocks of cyclotomic Hecke algebras, arXiv:math/0607451v4, PDF p. 16, Theorem 3.19

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P29

namespace QAlgorithms.Papers.Independent.Intake100.P29

noncomputable section

open scoped BigOperators Classical

variable {F : Type} [Field F]

/-- Theorem 3.19, PDF pp. 16--17. Q is arbitrary nonzero: a single q-orbit
is a proof reduction, not a hypothesis of the displayed theorem. -/
theorem residue_iff_jantzen {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (q : F) (hq : q ≠ 0) (hqOne : q ≠ 1) (Q : Fin r → F) (hQ : ∀ a, Q a ≠ 0)
    (L M : Multipartition r) (hL : size L = n) (hM : size M = n) :
    FieldResidueEquivalent q Q L M ↔ JantzenEquivalent q Q L M := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P29
