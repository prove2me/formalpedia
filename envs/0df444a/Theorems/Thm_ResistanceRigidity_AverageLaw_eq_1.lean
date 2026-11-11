-- Prove2me | Theorems.Thm_ResistanceRigidity_AverageLaw_eq_1
-- name    : ResistanceRigidity.AverageLaw.eq_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:06:24.731684+00:00
-- url     : https://prove2.me/theorems/23ce2daa-5b8b-4935-8b5c-6642f47f1595
-- title:
--   §2, eq. (1) — $R = z\mathbf 1^\top + \mathbf 1 z^\top - 2Q$ and $x^\top Q x = -\tfrac12 x^\top R x$ for $\mathbf 1^\top x = 0$
-- statement:
--   Let $G$ be a connected weighted graph on a finite vertex set $V$ with $N \ge 2$ vertices, given by its conductance function $c$ (symmetric, nonnegative, zero on the diagonal). Let $L$ be its Laplacian, $Q = L^+$ the Moore–Penrose pseudoinverse, $z = \mathrm{diag}(Q)$, and $R$ the matrix of effective resistances $R_{uv} = (e_u - e_v)^\top Q (e_u - e_v)$. Then
--   $$R = z\mathbf 1^\top + \mathbf 1 z^\top - 2Q,$$
--   and consequently, for every vector $x \in \mathbb R^V$ with $\mathbf 1^\top x = 0$,
--   $$x^\top Q x = -\tfrac12\, x^\top R x .$$
--
--   This is the first of the four facts of §2. It converts quadratic forms of the pseudoinverse on zero-sum vectors into quadratic forms of the resistance matrix; the local identity (4) and the equality analysis of Theorem 3.1 are derived from it.
--
--   Differences from the source:
--   - encoding: a graph with positive edge conductances $w$, $w_{uv} = 0$ off the edges and on the diagonal → a conductance function $c : V \to V \to \mathbb R$ that is symmetric, nonnegative and zero on the diagonal, edges being the pairs with $c > 0$; reason: the same weighted graphs.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 5, §2, eq. (1)

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Matrices

open Matrix

namespace ResistanceRigidity.AverageLaw

/-- §2, eq. (1): on a connected weighted graph with at least two vertices,
`R = z 1ᵀ + 1 zᵀ − 2Q` with `Q = L⁺`, `z = diag(Q)`, and `xᵀ Q x = −(1/2) xᵀ R x` for every
`x` with `1ᵀ x = 0`. -/
theorem eq_1 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 2 ≤ Fintype.card V) :
    resMat c = vecMulVec (diagPinv c) (fun _ => (1 : ℝ)) + vecMulVec (fun _ => (1 : ℝ)) (diagPinv c)
        - (2 : ℝ) • pinvLap c ∧
      ∀ x : V → ℝ, ∑ v, x v = 0 →
        x ⬝ᵥ (pinvLap c *ᵥ x) = -(1 / 2 : ℝ) * (x ⬝ᵥ (resMat c *ᵥ x)) := by sorry

end ResistanceRigidity.AverageLaw
