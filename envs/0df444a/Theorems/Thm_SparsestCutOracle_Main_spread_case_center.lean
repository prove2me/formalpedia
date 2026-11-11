-- Prove2me | Theorems.Thm_SparsestCutOracle_Main_spread_case_center
-- name    : SparsestCutOracle.Main.spread_case_center
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:44:00.069614+00:00
-- url     : https://prove2.me/theorems/2f22884d-d05c-431d-a911-1d4123d80447
-- title:
--   Lemma 6 — A spread subset and a center
-- statement:
--   Here $V$ has positive integer size $n$, $\Pi=\sum_i\pi(i)$, $D_\pi=\operatorname{diag}(\pi)$, and $K_\pi=\Pi D_\pi-\pi\pi^\top$. Write $d_X(i,j)=X_{ii}+X_{jj}-2X_{ij}$ and $r_0=1/(2\sqrt{10})$; balls are defined using this squared distance.
--
--   Let $\pi>0$ and let $X$ be a normalized positive semidefinite Gram matrix with $\frac45\Pi^2\le K_\pi\mathbin\bullet X\le\Pi^2$. Assume every $r_0$-ball has weight below $\Pi/4$. The deterministic finite center search succeeds. For its center $i_0$ and $A=B(i_0,4)$,
--
--   $$i_0\in A,\quad\pi(A)\ge\Pi/2,\quad d_X(i,i_0)\le16\ (i\in A),\quad
--   \sum_{i,j\in A}\pi(i)\pi(j)d_X(i,j)\ge\Pi^2/320.$$
--
--   This records both the bounded radius and the ordered-pair spread lower bound. All constants remain the printed constants.
--
--   Differences from the source:
--   - encoding: we can find A and i₀ → a deterministic search through all candidate centers, with A the radius-four ball; reason: the proof identifies exactly such a ball and the lemma states no running-time bound
--   - encoding: Gram vectors in an unspecified Euclidean realization → squared distances computed directly from their positive semidefinite Gram matrix; reason: norms and distances are invariant under the choice of realization; the positive integer vertex domain excludes the empty set
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), p. 24, Lemma 6 and Equation (10)

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Geometry

namespace SparsestCutOracle.Main

/-- Lemma 6, p.24: the finite center search succeeds and its radius-four ball works. -/
theorem spread_case_center {n : ℕ} (hn : 1 ≤ n) (π : Fin n → ℝ)
    (hπ : ∀ v, 0 < π v) (X : Mat n) (hX : X.PosSemidef)
    (htrace : dot (D π) X = totalWeight π)
    (hlower : (4 / 5 : ℝ) * totalWeight π ^ 2 ≤ dot (K π) X)
    (hupper : dot (K π) X ≤ totalWeight π ^ 2)
    (hballs : ∀ i, mass π (ball X i r₀) < totalWeight π / 4) :
    ∃ i₀ : Fin n, spreadCenter π X = some i₀ ∧
      let A := ball X i₀ 4
      i₀ ∈ A ∧ totalWeight π / 2 ≤ mass π A ∧
      (∀ i ∈ A, sqdist X i i₀ ≤ 16) ∧
      (1 / 320 : ℝ) * totalWeight π ^ 2 ≤ spread π X A := by sorry

end SparsestCutOracle.Main
