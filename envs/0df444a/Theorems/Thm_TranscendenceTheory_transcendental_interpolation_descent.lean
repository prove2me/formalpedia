-- Prove2me | Theorems.Thm_TranscendenceTheory_transcendental_interpolation_descent
-- name    : TranscendenceTheory.transcendental_interpolation_descent
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-19T16:30:37.946598+00:00
-- url     : https://prove2.me/theorems/78625487-e696-4283-9db0-6dc6274cfa29
-- title:
--   Transcendental interpolation descends to scalar systems
-- statement:
--   Let $K$ be a field, $L$ a commutative $K$-algebra, and
--
--   $$\varphi:K[T]\hookrightarrow L$$
--
--   an injective $K$-algebra homomorphism. Write $t=\varphi(T)$. Let $I$ be a finite index set, $b$ a nonnegative integer, $c\in K$, $V_{i,j}(Z)\in K[Z]$ for $i\in I$ and $j\ge0$, and $Q(Z)\in K[Z]$. A bar denotes extension of coefficients from $K$ to $L$.
--
--   The following conditions are equivalent:
--
--   1. There is one family of weights $w_i\in L$ satisfying, simultaneously for $0\le j\le b$,
--
--      $$(1-\overline c Z)\sum_{i\in I}w_i\overline{V_{i,j}}(Z)=t^j\overline Q(Z).$$
--
--   2. For each $k$ with $0\le k\le b$, there is one family of scalar weights $u_{k,i}\in K$ satisfying, simultaneously for $0\le j\le b$,
--
--      $$(1-cZ)\sum_{i\in I}u_{k,i}V_{i,j}(Z)=\delta_{kj}Q(Z).$$
--
--   Here $\delta_{kj}$ is one when $k=j$ and zero otherwise. The family may depend on $k$, but each family must solve all the equations indexed by $j$.
--
--   This converts exact interpolation with transcendental right-hand sides into finitely many systems over the coefficient field. No degree assumption is imposed on the $V_{i,j}$ or on $Q$. The statement includes $b=0$, $c=0$, $Q=0$, and an empty index set.
-- source:
--   Derived linear-algebra reduction of the exact-interpolation clause in https://prove2.me/theorems/6b3b6a47-f0a5-48cd-8609-9cab71006042. The primary linear-algebra input is Mathlib, revision 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/LinearAlgebra/Basis/VectorSpace.lean, LinearMap.exists_leftInverse_of_injective (lines 240 onward): https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Basis/VectorSpace.lean#L240. Polynomial coefficient and scalar-extension APIs: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/AlgebraMap.lean. The displayed descent equivalence is a derived lemma, not a quotation from the mission paper. Mission context: Senthil Kumar K, Algebraic independence of values of Weierstrass elliptic and zeta functions (2026), Appendix A.2, Theorem A.3 and Proposition A.1, https://doi.org/10.1017/S001309152610145X. The parent is preserved outside its exact-interpolation exclusion clause; the same hypotheses, root applicability condition, witnesses and numerical bound are retained. Separate Lean proofs check both directions. The uniform geometric estimate remains open.

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose

open scoped BigOperators
open Polynomial

theorem TranscendenceTheory.transcendental_interpolation_descent
    (K L ι : Type*) [Field K] [CommRing L] [Algebra K L] [Fintype ι]
    (φ : Polynomial K →ₐ[K] L) (hφ : Function.Injective φ)
    (b : ℕ) (c : K) (V : ι → ℕ → Polynomial K) (Q : Polynomial K) :
    (∃ w : ι → L, ∀ j ≤ b,
      (1 - Polynomial.C (algebraMap K L c) * Polynomial.X) *
        (∑ i, Polynomial.C (w i) * (V i j).map (algebraMap K L)) =
          Polynomial.C ((φ Polynomial.X) ^ j) * Q.map (algebraMap K L)) ↔
    (∀ k ≤ b, ∃ u : ι → K, ∀ j ≤ b,
      (1 - Polynomial.C c * Polynomial.X) *
        (∑ i, Polynomial.C (u i) * V i j) = if k = j then Q else 0) := by sorry
