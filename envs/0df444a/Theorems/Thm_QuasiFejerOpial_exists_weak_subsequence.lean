-- Prove2me | Theorems.Thm_QuasiFejerOpial_exists_weak_subsequence
-- name    : QuasiFejerOpial.exists_weak_subsequence
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-23T11:47:53.033098+00:00
-- url     : https://prove2.me/theorems/17905530-1e14-4a39-857c-87e5e1a2e447
-- title:
--   Every bounded sequence in a real Hilbert space has a weakly convergent subsequence
-- statement:
--   Let $H$ be a real Hilbert space and let $(x_n)_{n\ge0}$ be a norm-bounded sequence: there is a real $R$ such that $\|x_n\|\le R$ for every $n$. Then there are a strictly increasing map $r:\mathbb N\to\mathbb N$ and a point $p\in H$ such that $x_{r(k)}\rightharpoonup p$. Here weak convergence means $\langle x_{r(k)},y\rangle\to\langle p,y\rangle$ for every $y\in H$. No separability or finite-dimensionality assumption is imposed on $H$. This is weak sequential compactness for bounded sequences in a Hilbert space, used as the compactness step in quasi-Fejer/Opial convergence arguments.
-- source:
--   University of Waterloo PMATH453, Chapter 2: Hilbert Spaces, Theorem 2.47, printed page 13 (PDF page 13), https://www.math.uwaterloo.ca/~snew/PMATH453/Chap2HilbertSpaces.pdf . Real-Hilbert-space specialization of the stated weak subsequence theorem.

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
open Filter Topology InnerProductSpace
open ThreeOpSplitting.Convergence
universe u

namespace QuasiFejerOpial
theorem exists_weak_subsequence {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : ℕ → E) (R : ℝ) (hR : ∀ n, ‖x n‖ ≤ R) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ p : E, WeakTendsto (x ∘ r) p := by sorry

end QuasiFejerOpial
