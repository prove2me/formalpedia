-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_det_eq_zero_iff_circuit
-- name    : WhitneyMatroid.Fano.det_eq_zero_iff_circuit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:13:27.359747+00:00
-- url     : https://prove2.me/theorems/32366d48-7b81-4cff-a5b7-22b782dd7455
-- title:
--   Theorem 32 — vanishing minors of a circuit matrix and circuits avoiding a set
-- statement:
--   Let $\mathbf M'$ be a real matrix whose matroid $M'$ has elements $e_1,\dots,e_n$, and let $\mathbf M$ be a circuit matrix of $\mathbf M'$. Let $P_1,\dots,P_q$ form a strict fundamental set of circuits in $M'$ with respect to $e_{n-q+1},\dots,e_n$, and let the first $q$ rows of $\mathbf M$ be those corresponding to $P_1,\dots,P_q$. Let $i_1<\cdots<i_s$ be numbers from $\{1,\dots,q\}$, $j_1<\cdots<j_s$ numbers from $\{1,\dots,n-q\}$, and $i'_1<\cdots<i'_{q-s}$ the complement of $\{i_1,\dots,i_s\}$ in $\{1,\dots,q\}$. Let
--
--   - $D$ be the determinant of $\mathbf M$ with rows $i_1,\dots,i_s$ and columns $j_1,\dots,j_s$;
--   - $D'$ be the determinant of $\mathbf M$ with rows $1,\dots,q$ and columns $j_1,\dots,j_s,\ n-q+i'_1,\dots,n-q+i'_{q-s}$.
--
--   Then
--
--   $$
--   D=0\iff D'=0\iff \text{some circuit } P \text{ of } M' \text{ contains none of } e_{j_1},\dots,e_{j_s},e_{n-q+i'_1},\dots,e_{n-q+i'_{q-s}}.
--   $$
--
--   The theorem turns the combinatorics of $M'$ into polynomial equations on the entries of a normalised circuit matrix; Whitney applies it in §16 to the triples $(1,4;1,2)$, $(2,4;1,3)$, $(3,4;2,3)$ and $(1,2,3;1,2,3)$ to show that the Fano matroid has no real matrix.
--
--   **Formalization Note** The elements are `Fin (p + q)` with $n=p+q$: $e_j$ ($1\le j\le n-q$) is `Fin.castAdd q (j-1)` and $e_{n-q+i}$ ($1\le i\le q$) is `Fin.natAdd p (i-1)`. The row of $P_i$ is `k (i-1)`. The increasing lists $i_\bullet$, $j_\bullet$, $i'_\bullet$ are order embeddings `I : Fin s ↪o Fin q`, `J : Fin s ↪o Fin p`, `I' : Fin t ↪o Fin q` with $s+t=q$ and the range of `I'` the complement of the range of `I`; this avoids natural-number subtraction. The columns of $D'$ are listed in the paper's order with `Fin.append`. Only the vanishing of $D$ and $D'$ is asserted, so the order of rows and columns does not matter.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), pp. 528–529, Theorem 32

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_FundamentalCircuits
import Definitions.Def_WhitneyMatroid_Fano_IsCircuitMatrix

namespace WhitneyMatroid.Fano

/-- Whitney, Theorem 32 (pp. 528–529). The elements are `Fin (p + q)` with `n = p + q`: Whitney's
`e_j` (`1 ≤ j ≤ n − q`) is `Fin.castAdd q (j-1)` and `e_{n−q+i}` (`1 ≤ i ≤ q`) is
`Fin.natAdd p (i-1)`. `B` (Whitney's `𝐌`) is the circuit matrix of the real matrix `A`
(Whitney's `𝐌′`), whose matroid is `M′`; the circuits `P_i = row (k i)` form a strict fundamental
set of circuits in `M′` with respect to `e_{n−q+1}, …, e_n`, and the rows `B (k i)` are "the first
`q` rows". `I` lists `i₁ < ⋯ < i_s` from `{1, …, q}`, `J` lists `j₁ < ⋯ < j_s` from
`{1, …, n − q}`, and `I'` lists the complementary `i′₁ < ⋯ < i′_{q−s}` (`t = q − s`). Then the
determinant `D` of `B` with rows `i₁, …, i_s` and columns `j₁, …, j_s` vanishes iff the
determinant `D′` with rows `1, …, q` and columns `j₁, …, j_s, n−q+i′₁, …, n−q+i′_{q−s}` vanishes,
iff some circuit of `M′` contains none of the columns `e_{j₁}, …, e_{j_s}, e_{n−q+i′₁}, …,
e_{n−q+i′_{q−s}}`. -/
theorem det_eq_zero_iff_circuit {p q m : ℕ} {κ : Type*}
    (A : Matrix (Fin m) (Fin (p + q)) ℝ) (M' : Matroid (Fin (p + q)))
    (B : Matrix κ (Fin (p + q)) ℝ) (row : κ ≃ {P : Set (Fin (p + q)) // M'.IsCircuit P})
    (hB : IsCircuitMatrix M' A B row) (k : Fin q → κ)
    (hP : IsStrictFundamentalCircuitSetWrt M' (fun i => (row (k i) : Set (Fin (p + q))))
      (Fin.natAdd p))
    {s t : ℕ} (hst : s + t = q) (I : Fin s ↪o Fin q) (J : Fin s ↪o Fin p) (I' : Fin t ↪o Fin q)
    (hI' : ∀ i : Fin q, i ∈ Set.range I' ↔ i ∉ Set.range I) :
    let D : ℝ := (Matrix.of fun a b : Fin s => B (k (I a)) (Fin.castAdd q (J b))).det
    let cols : Fin (s + t) → Fin (p + q) :=
      Fin.append (fun b : Fin s => Fin.castAdd q (J b)) (fun c : Fin t => Fin.natAdd p (I' c))
    let D' : ℝ := (Matrix.of fun (i c : Fin q) => B (k i) (cols (Fin.cast hst.symm c))).det
    (D = 0 ↔ D' = 0) ∧
      (D = 0 ↔
        ∃ P : Set (Fin (p + q)), M'.IsCircuit P ∧ ∀ c : Fin (s + t), cols c ∉ P) := by sorry

end WhitneyMatroid.Fano
