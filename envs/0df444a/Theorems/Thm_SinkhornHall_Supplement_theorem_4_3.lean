-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_theorem_4_3
-- name    : SinkhornHall.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:12:09.745659+00:00
-- url     : https://prove2.me/theorems/88783c63-3545-4442-bd2b-d07de24be130
-- title:
--   Theorem 4.3 (companion theorem) — for $\ell>16n^6\log(nA_{\max}/A_{\min})$ the sorted marginals output every extreme Hall blocker
-- statement:
--   Setting of §4: $A$ is a nonnegative $n\times n$ matrix with no zero row or column (its support graph $G=G(A)$ has no isolated node), the marginals are $(r,c)=(\mathbf 1,\mathbf 1)$, $A_{\max}$ is the largest entry and $A_{\min}$ the least positive entry of $A$, and $(M_k,N_k)$ is the Sinkhorn sequence $N_0=C(A)$, $M_k=R(N_k)$, $N_{k+1}=C(M_k)$. A row set $X$ is an **extreme Hall blocker** if $X\sqcup([n]\setminus\Gamma(X))$ is an extreme stable set (for $(r,c)=(\mathbf 1,\mathbf 1)$) and $|\Gamma(X)|<|X|$, where $\Gamma(X)$ is the set of columns adjacent to $X$.
--
--   **Algorithm (Sinkhorn & Sorting Marginals).** Step 0: $A\leftarrow C(A)$. Step 1: repeat $A\leftarrow C(R(A))$ $\ell$ times. Step 2: let $p=A\mathbf 1$ and sort $p_{i_1}\le\dots\le p_{i_n}$. Step 3: output $U_k=\{i_1,\dots,i_k\}$ for $k=0,1,\dots,n$.
--
--   Suppose $G$ has no perfect matching. If
--
--   $$\ell>16\,n^6\log\frac{nA_{\max}}{A_{\min}},$$
--
--   then the output contains all extreme Hall blockers: for every sort in step 2, every extreme Hall blocker equals some $U_k$.
--
--   This is the paper's second algorithm: a polynomial number of Sinkhorn iterations followed by one sort of the row marginals finds every extreme Hall blocker, among them one maximizing $|X|-|\Gamma(X)|$.
--
--   Differences from the source:
--   - encoding: the matrix after step 1 → $N_\ell$ of the Sinkhorn sequence (2.6) with $(r,c)=(\mathbf 1,\mathbf 1)$; reason: p.17 states that in step 2 the matrix equals $N_\ell$
--   - encoding: "the output contains" → for every tie-break $\sigma$ of the sort ($p\circ\sigma$ monotone), every extreme Hall blocker is $\sigma(\{0,\dots,k-1\})$ for some $k\le n$; reason: the sort is nondeterministic; 0-based indices
--   - encoding: $\log$ → `Real.log`, strict threshold with $n$ the side length; reason: the paper's reading
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Theorem 4.3, p.16 (proof p.17); Algorithm: Sinkhorn & Sorting Marginals, p.16

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Theorem 4.3 (extreme Hall blockers from marginals).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Theorem 4.3, p.16: "Suppose that G has no perfect
matching. For ℓ > 16n⁶ log nA_max/A_min, the output contains all extreme Hall blockers."

The algorithm is "Sinkhorn & Sorting Marginals" (§4.2, p.16): step 0 `A ← C(A)`; step 1 repeats
`A ← C(R(A))` `ℓ` times; step 2 sets `p := A1` and sorts `p_{i_1} ≤ ⋯ ≤ p_{i_n}`; step 3 outputs
`U_k := {i_1, …, i_k}` for `k = 0, …, n`. Setting of §4 (p.15): `G = G(A)` for a nonnegative
`n × n` matrix `A` with no isolated node (no zero row or column), `(r, c) = (1, 1)`, `A_max` the
largest and `A_min` the least positive entry. An extreme Hall blocker is a row set `X` with
`X ⊔ ([n] \ Γ(X))` an extreme stable set and `|Γ(X)| < |X|` (p.16).

**Formalization Note.** After step 1 the matrix is `N_ℓ = sinkhornN A 1 1 ℓ` (p.17: "In the step 2
of the algorithm, the matrix A equals N_ℓ"). The conclusion holds for every tie-break `σ` of the
sort (`p ∘ σ` monotone): every extreme Hall blocker equals some prefix `U_k`, `k ≤ n`. `log` is
`Real.log`, `n` is the side length, and the threshold is strict. -/
theorem theorem_4_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (hpm : ¬ SinkhornHall.HasPerfectMatching A) (ℓ : ℕ)
    (hℓ : 16 * (n : ℝ) ^ 6 * Real.log ((n : ℝ) * SinkhornHall.Amax A / SinkhornHall.Amin A) < ℓ)
    (σ : Equiv.Perm (Fin n)) (hσ : Monotone ((fun i => ∑ j, sinkhornN A 1 1 ℓ i j) ∘ σ)) :
    ∀ X : Finset (Fin n), IsExtremeSubset A X → SinkhornHall.IsHallBlocker A X →
      ∃ k ≤ n, X = sortPrefix σ k := by sorry

end SinkhornHall.Supplement
