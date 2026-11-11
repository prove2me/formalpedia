-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_rigidification
-- name    : SymmetricDepthHierarchy.ConstantDepth.rigidification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:44.144732+00:00
-- url     : https://prove2.me/theorems/17aecf6f-863b-4579-a6b7-b36ba96558ff
-- title:
--   Lemma 2.4 (Rigidification): a reduced matrix-symmetric circuit with no larger size, depth or orbit size
-- statement:
--   Let $n\ge1$ and let $C$ be a matrix-symmetric algebraic circuit over the variables $X_n=\{x_{i,j}\}$ and a field $K$ of characteristic zero. Then there is a **reduced** matrix-symmetric circuit $C'$ computing the same polynomial as $C$ such that
--   $$\operatorname{size}(C')\le\operatorname{size}(C),\qquad \operatorname{depth}(C')\le\operatorname{depth}(C),\qquad \operatorname{maxOrb}(C')\le\operatorname{maxOrb}(C).$$
--
--   Every symmetric circuit may thus be assumed reduced (hence rigid), which is what the support theorem and the characterisation require.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, variables x_{i,j} → Fin n (0-based), variables indexed by Fin n × Fin n; reason: relabelling of [n]; the same polynomials and circuits
--   - encoding: depth: maximum number of wires on an input-to-output path → depth = that maximum, read as 0 when no input-to-output path exists; reason: the maximum of the empty set occurs only for circuits without input gates
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 8 (PDF p. 11), Lemma 2.4; proof in Appendix A, p. 27 (PDF p. 30)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Lemma 2.4 (Rigidification), printed p. 8 (PDF p. 11). For every matrix-symmetric circuit `C`
there is a reduced matrix-symmetric circuit `C'` computing the same polynomial whose size, depth and
orbit size are at most those of `C`. -/
theorem rigidification {K : Type} [Field K] [CharZero K] {n : ℕ} (hn : 1 ≤ n)
    {V : Type} [Fintype V] (C : Circuit K n V) (hC : C.WellFormed) (hsym : C.MatrixSymmetric) :
    ∃ (V' : Type) (_ : Fintype V') (C' : Circuit K n V'),
      C'.WellFormed ∧ C'.MatrixSymmetric ∧ C'.Reduced ∧
      C'.value C'.out = C.value C.out ∧
      C'.size ≤ C.size ∧ C'.depth ≤ C.depth ∧ C'.maxOrb ≤ C.maxOrb := by sorry

end SymmetricDepthHierarchy.ConstantDepth
