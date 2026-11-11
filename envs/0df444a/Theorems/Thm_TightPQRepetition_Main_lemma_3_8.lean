-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_3_8
-- name    : TightPQRepetition.Main.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:34:31.815008+00:00
-- url     : https://prove2.me/theorems/b29b5f2f-c119-4573-8ff1-cc91000fdf5a
-- title:
--   Lemma 3.8 — Jordan's lemma (corrected: finite-dimensional $\mathcal H$)
-- statement:
--   For any two Hermitian projectors $\Pi_A,\Pi_B$ on a finite-dimensional complex inner product space $\mathcal H$, of any dimension, there is an orthogonal decomposition $\mathcal H=\bigoplus_jS_j$ into one- and two-dimensional subspaces, each invariant under both projectors, such that on each one-dimensional subspace both act as the identity or as zero, and on each two-dimensional subspace both are rank-one projectors, onto $|v_j\rangle$ and $|w_j\rangle$ respectively, of distinct orthonormal bases $\{|v_j\rangle,|v_j^\perp\rangle\}$ and $\{|w_j\rangle,|w_j^\perp\rangle\}$. The singular values are $\varsigma_j=\langle w_j|v_j\rangle$, and the degenerate labelling of one-dimensional subspaces is the convention following the lemma.
--
--   This is the structure behind the singular value decomposition $\Pi_B\Pi_A=\sum_j\varsigma_j|w_j\rangle\langle v_j|$ used in Theorem 3.9.
--
--   Differences from the source:
--   - correction: a Hilbert space → every finite-dimensional complex inner product space; reason: false in infinite dimensions: on L²[0,1]⊗ℂ² with Π_A = I⊗|0⟩⟨0| and Π_B the projection on f(x)(cos θ(x)|0⟩ + sin θ(x)|1⟩), θ(x) = πx/4 + π/8, Π_AΠ_BΠ_A is multiplication by cos²θ(x), which has no eigenvector, while a block of dimension at most two would give one; every register of the paper is finitely many qubits
--   - reading: distinct orthonormal bases → 0 < ς_j < 1 on two-dimensional blocks, with ς_j = ⟨w_j|v_j⟩ ≥ 0 after choosing phases; reason: the two bases, as sets of rays, are then distinct, and a block where they coincide splits into one-dimensional blocks
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 3.8 and the convention following it, printed p. 12 / PDF p. 14

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Jordan

namespace TightPQRepetition.Main

/-- Lemma 3.8 (printed p. 12, PDF p. 14). -/
theorem lemma_3_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (PA PB : H →L[ℂ] H) (hA : IsHermitianProjector PA)
    (hB : IsHermitianProjector PB) :
    Nonempty (JordanDecomposition PA PB) := by sorry

end TightPQRepetition.Main
