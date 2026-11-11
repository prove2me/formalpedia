-- Prove2me | Theorems.Thm_ResistanceRigidity_AverageLaw_eq_8
-- name    : ResistanceRigidity.AverageLaw.eq_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:06:23.443222+00:00
-- url     : https://prove2.me/theorems/e256d30d-12bd-48a2-bb51-bbe14130e7ae
-- title:
--   §3, eq. (8) — $LR = (Lz)\mathbf 1^\top - 2P$, $-c_u = (Lz)_u - 2r/N$, and $LR = -2P$ when every $c_u = 2r/N$
-- statement:
--   Let $G$ be a connected weighted graph on a finite vertex set $V$ with $N \ge 2$ vertices and conductance function $c$ (symmetric, nonnegative, zero on the diagonal). Let $L$ be its Laplacian, $Q = L^+$, $z = \mathrm{diag}(Q)$, $P = I - \frac1N J$, $R$ the resistance matrix, $r = N - 1$ and $c_u = \sum_v c(u,v) R_{uv}$. Then
--   $$LR = (Lz)\mathbf 1^\top - 2P,$$
--   whose diagonal entry at $u$ reads
--   $$-c_u = (Lz)_u - \frac{2r}{N}.$$
--   Hence, if $c_u = 2r/N$ for every vertex $u$, then $Lz = 0$ and
--   $$LR = -2P.$$
--
--   The first identity is Lemma 1 of Bapat (2004). In the proof of Theorem 3.1 the equality case $0 < \varepsilon < 1$ yields $c_u = 2r/N$ at every vertex, and the resulting $LR = -2P$ shows that the graph has diameter two and is strongly regular.
--
--   Differences from the source:
--   - encoding: a graph with positive edge conductances $w$, $w_{uv} = 0$ off the edges and on the diagonal → a conductance function $c : V \to V \to \mathbb R$ that is symmetric, nonnegative and zero on the diagonal, edges being the pairs with $c > 0$; reason: the same weighted graphs.
--   - generalization: derived inside the proof of Theorem 3.1, for a graph on $N \ge 3$ vertices in the equality case with $0 < \varepsilon < 1$ → every connected graph on $N \ge 2$ vertices, with only the hypothesis "$c_u = 2r/N$ for every $u$" for the final conclusion; reason: the derivation on the page uses nothing else (it is the general identity of Bapat), and the source's situation is a special case.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 7, §3, proof of Theorem 3.1, eq. (8)

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Matrices

open Matrix

namespace ResistanceRigidity.AverageLaw

/-- §3, eq. (8): on a connected weighted graph with at least two vertices,
`L R = (L z) 1ᵀ − 2P`; its diagonal entry at `u` reads `−c_u = (L z)_u − 2r/N` with
`r = N − 1`; hence, if `c_u = 2r/N` at every vertex, `L z = 0` and `L R = −2P`. -/
theorem eq_8 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 2 ≤ Fintype.card V) :
    IncrementalER.lap c * resMat c =
        vecMulVec (IncrementalER.lap c *ᵥ diagPinv c) (fun _ => (1 : ℝ)) - (2 : ℝ) • projOnes V ∧
      (∀ u : V, -IncrementalER.levDeg c u =
        (IncrementalER.lap c *ᵥ diagPinv c) u
          - 2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) ∧
      ((∀ u : V, IncrementalER.levDeg c u = 2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) →
        IncrementalER.lap c *ᵥ diagPinv c = 0 ∧
          IncrementalER.lap c * resMat c = -((2 : ℝ) • projOnes V)) := by sorry

end ResistanceRigidity.AverageLaw
