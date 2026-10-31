-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P06_bmw_strand_map
-- name    : QAlgorithms.Papers.Independent.Intake100.P06.bmw_strand_map
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:44:54.193187+00:00
-- url     : https://prove2.me/theorems/415e57df-2340-4946-a8b3-b4ca5043078d
-- title:
--   Canonical BMW strand map and conditional injectivity
-- statement:
--   Let $S$ be a commutative unital ring, let $r\ge1$, and let $\rho,q,\delta_0,u_1,\ldots,u_r$ be units of $S$. Let $\delta_j\in S$ be specified for every $j\ge0$, with $\rho^{-1}-\rho=(q^{-1}-q)(\delta_0-1)$. Write $W_{n,S,r}$ for the algebra with all the affine BMW relations of Definition 2.3 and the relation $\prod_{i=1}^r(y_1-u_i)=0$.
--
--   For every $n\ge0$, the assignment sending every existing generator $e_i,g_i^{\pm1},y_1^{\pm1}$ to the same named generator at level $n+1$ defines an $S$-algebra homomorphism
--   $$\iota_n:W_{n,S,r}\longrightarrow W_{n+1,S,r}.$$
--   The generator $y_1$ is absent at level zero. If $S$ is an integral domain and the parameters are admissible, then $\iota_n$ is injective. Here admissibility means that $q-q^{-1}$ is nonzero and regular, all integer-shift moment relations of Definition 4.1 hold, and $(y_1^je_1)_{0\le j<r}$ is $S$-linearly independent in $W_{2,S,r}$. Negative moments have the geometric sign correction to (4.1).
--
--   This gives the canonical BMW tower maps while keeping their unconditional existence separate from conditional injectivity.
-- source:
--   Cyclotomic Birman--Wenzl--Murakami algebras, I: Freeness and realization as tangle algebras, arXiv:math/0612064v5, PDF p. 27, Remark 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06

noncomputable section

open scoped BigOperators Classical TensorProduct

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

/-- Remark 3.2, PDF p.27: the generator-preserving strand map exists over every
valid ring; injectivity additionally requires admissibility and a domain.
Definition 5.3 is read through condition (1). The accepted negative moments
use the geometrically forced PLUS correction to printed (4.1), PDF p.31. -/
theorem bmw_strand_map {S : Type*} [CommRing S] {r : ℕ}
    (P : GroundParameters S r) (n : ℕ) :
    ∃ f : BMW P n →ₐ[S] BMW P (n + 1),
      (∀ i : ℕ, i + 1 < n → f (bmwE P n i) = bmwE P (n + 1) i) ∧
      (∀ i : ℕ, i + 1 < n → ∀ inverse : Bool,
        f (bmwG P n i inverse) = bmwG P (n + 1) i inverse) ∧
      (1 ≤ n → ∀ inverse : Bool,
        f (bmwY P n inverse) = bmwY P (n + 1) inverse) ∧
      (BMWAdmissible P → IsDomain S → Function.Injective f) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P06

end
