-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_circuitMatrix_fundamental_rows_base
-- name    : WhitneyMatroid.Fano.circuitMatrix_fundamental_rows_base
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:12:59.540315+00:00
-- url     : https://prove2.me/theorems/a779fc39-b0b2-4def-a9ff-bc9cead79359
-- title:
--   Theorem 29 — the rows of a fundamental set of circuits span the circuit matrix
-- statement:
--   Let $\mathbf M$ be a real $m\times n$ matrix, $M$ its matroid, and $\mathbf M'$ a circuit matrix of $\mathbf M$ (one row per circuit of $M$, the row of a circuit $P$ satisfying (14.1)). Let $P_1,\dots,P_q$ be a fundamental set of circuits in $M$ (§9; in particular $q=n(M)$), and let $R'_1,\dots,R'_q$ be the corresponding rows of $\mathbf M'$. Then:
--
--   1. $R'_1,\dots,R'_q$ are linearly independent;
--   2. every row of $\mathbf M'$ is a linear combination of $R'_1,\dots,R'_q$;
--   3. hence
--   $$
--   r(\mathbf M')=q=n(M).
--   $$
--
--   In the paper's notation of Theorem 29, $\mathbf M$ is the given matrix and $\mathbf M'$ its circuit matrix. The theorem identifies the dimension of the row space of the circuit matrix with the nullity, which underlies the duality of a matrix and its circuit matrix (Theorems 30, 31) and the determinant criterion of Theorem 32.
--
--   **Formalization Note** The fundamental set is given by a list $k_1,\dots,k_q$ of row indices of $\mathbf M'$, the circuit $P_i$ being the circuit of row $k_i$. The rank $r(\mathbf M')$ is Mathlib's `Matrix.rank`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 527, Theorem 29

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_FundamentalCircuits
import Definitions.Def_WhitneyMatroid_Fano_IsCircuitMatrix

namespace WhitneyMatroid.Fano

/-- Whitney, Theorem 29 (p. 527). Here `A` is Whitney's matrix `𝐌`, `M` its matroid, and `B` its
circuit matrix `𝐌′`. If the circuits `P_i = row (k i)` (`i < q`) form a fundamental set of
circuits in `M`, then the corresponding rows `B (k i)` of `B` form a base for the rows of `B`
(they are linearly independent and every row of `B` is a linear combination of them); hence the
rank of `B` is `q = n(M)`. -/
theorem circuitMatrix_fundamental_rows_base {ι : Type*} [Fintype ι] {m : ℕ} {κ : Type*}
    (A : Matrix (Fin m) ι ℝ) (M : Matroid ι) (B : Matrix κ ι ℝ)
    (row : κ ≃ {P : Set ι // M.IsCircuit P}) (hB : IsCircuitMatrix M A B row)
    {q : ℕ} (k : Fin q → κ) (hP : IsFundamentalCircuitSet M (fun i => (row (k i) : Set ι))) :
    LinearIndependent ℝ (fun i => B (k i)) ∧
      (∀ k' : κ, B k' ∈ Submodule.span ℝ (Set.range fun i => B (k i))) ∧
      B.rank = q := by sorry

end WhitneyMatroid.Fano
