-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapE01_hypergraphProduct_parameters
-- name    : QAlgorithms.Papers.RoadmapE01.hypergraphProduct_parameters
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:28:20.594611+00:00
-- url     : https://prove2.me/theorems/9972356c-883d-4979-9b9e-99c770bf8b10
-- title:
--   Hypergraph-product CSS code: length, dimension, distance, and check weights
-- statement:
--   Let $H\in\mathbb F_2^{r\times n}$ have linearly independent rows, where $n=r+k$, and let $C=\ker H$. Write $d$ for the minimum Hamming weight of a nonzero word of $C$, with $d=\infty$ when $C=\{0\}$. Form the two parity-check matrices
--
--   $$
--   H_X=(H\otimes I_n\mid I_r\otimes H^{\mathsf T}),\qquad
--   H_Z=(I_n\otimes H\mid H^{\mathsf T}\otimes I_r).
--   $$
--
--   The qubit coordinates are the disjoint union $([n]\times[n])\sqcup([r]\times[r])$, explicitly reindexed as $[N]$ for $N=n^2+r^2$. Set $C_X=\ker H_X$ and $C_Z=\ker H_Z$. Then $\dim_{\mathbb F_2} C=k$, $H_XH_Z^{\mathsf T}=0$, and $C_Z^\perp\subseteq C_X$, so these matrices define a valid CSS code. Its parameters are
--
--   $$
--   \dim_{\mathbb F_2}(C_X/C_Z^\perp)=k^2,\qquad
--   \dim_{\mathbb C}\mathcal Q=2^{k^2},\qquad
--    d_Q=\min\!\left\{\min_{x\in C_X\setminus C_Z^\perp}|x|,
--                       \min_{z\in C_Z\setminus C_X^\perp}|z|\right\}=d.
--   $$
--
--   Here $\mathcal Q$ is the CSS coding subspace, $|\cdot|$ denotes Hamming weight, and an empty minimum is infinity. For every row index $a\in[r]$ and column index $b\in[n]$, the exact check weights are
--
--   $$
--   |(H_X)_{(a,b),\bullet}|=|H_{a,\bullet}|+|H_{\bullet,b}|,\qquad
--   |(H_Z)_{(b,a),\bullet}|=|H_{\bullet,b}|+|H_{a,\bullet}|.
--   $$
--
--   Consequently, if every row of $H$ has weight at most $u$ and every column has weight at most $v$, every row of either constructed check matrix has weight at most $u+v$. Bounds $u,v$ independent of blocklength therefore preserve the LDPC property; no regularity or self-orthogonality of the input code is required.
--
--   This construction transfers the classical code's minimum distance to a quantum CSS code while giving the exact logical dimension and preserving sparse checks.
-- source:
--   Quantum LDPC codes with positive rate and minimum distance proportional to n^{1/2}, arXiv:0903.0566v2, Theorem 1, PDF p. 3. https://arxiv.org/abs/0903.0566v2 . PDF SHA-256: 2b6b9e7541b358420c6d0e5120dea7c5314e4109453da6fa8a16e34c9a7522ea.

import Definitions.Def_QAlgorithms_Defs_HypergraphProducts
set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapE01

/-- Tillich--Zemor, arXiv:0903.0566v2, Theorem 1, PDF p.3.
The checks are the displayed construction on p.18 with both factors equal to H.
Quantum dimension counts logical qubits (p.4), while the coding space has
complex dimension 2^(k^2). Distance uses the explicit infinity convention
of p.15. The final implication gives the LDPC bound for any supplied uniform
row and column bounds, without imposing regularity on H. -/
theorem hypergraphProduct_parameters (r k : ℕ)
    (H : Matrix (Fin r) (Fin (r + k)) (ZMod 2))
    (hH : LinearIndependent (ZMod 2) H) :
    let N := (r + k) * (r + k) + r * r
    let e := HypergraphProduct.coordinateEquiv (r + k) (r + k) r r
    let HX : Matrix (Fin r × Fin (r + k)) (Fin N) (ZMod 2) :=
      (HypergraphProduct.checkVariable H H).submatrix id e.symm
    let HZ : Matrix (Fin (r + k) × Fin r) (Fin N) (ZMod 2) :=
      (HypergraphProduct.variableCheck H H).submatrix id e.symm
    let CX := FieldCodes.parityCheckCode HX
    let CZ := FieldCodes.parityCheckCode HZ
    let C := FieldCodes.parityCheckCode H
    Module.finrank (ZMod 2) C = k ∧
    HX * HZ.transpose = 0 ∧
    (∃ hCSS : codeDual CZ ≤ CX,
      BinaryCSS.logicalDimension CX CZ hCSS = k ^ 2 ∧
      Module.finrank ℂ (cssCode CX CZ) = 2 ^ (k ^ 2) ∧
      BinaryCSS.distance CX CZ hCSS = FieldCodes.minimumDistance C) ∧
    (∀ a : Fin r, ∀ b : Fin (r + k),
      hammingNorm (HX (a, b)) = hammingNorm (H a) + hammingNorm (fun i => H i b)) ∧
    (∀ b : Fin (r + k), ∀ a : Fin r,
      hammingNorm (HZ (b, a)) = hammingNorm (fun i => H i b) + hammingNorm (H a)) ∧
    (∀ rowBound colBound : ℕ,
      (∀ a, hammingNorm (H a) ≤ rowBound) →
      (∀ b, hammingNorm (fun i => H i b) ≤ colBound) →
      (∀ ab, hammingNorm (HX ab) ≤ rowBound + colBound) ∧
      (∀ ba, hammingNorm (HZ ba) ≤ rowBound + colBound)) := by sorry

end QAlgorithms.Papers.RoadmapE01
