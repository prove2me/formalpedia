-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_observations_4_2_4_3
-- name    : SmallSecretLWE.Classical.observations_4_2_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:58.813939+00:00
-- url     : https://prove2.me/theorems/4074bfc5-6303-4e14-b665-53a6e1da57cc
-- title:
--   Observations 4.2 and 4.3 — the vector $c$ of Construction 4.1 has $\|c\|_1\le T$ and $A^Tc=u_T-u_0$
-- statement:
--   Let $A\in\mathbb Z_q^{m\times n}$ have exactly $k$ nonzero entries in each row, $\lceil k/2\rceil\le l\le n$, and let $W=(u_0,u_1,\dots,u_T)$ be a walk in the Kikuchi graph $K_l(A)$. The vector $c\in\mathbb Z_q^m$ of Construction 4.1 satisfies
--   $$\|c\|_1\le T\qquad\text{and}\qquad A^Tc=u_T-u_0 .$$
--   So a walk of length $T$ whose endpoints are $\ell_1$-close yields a short vector $c$ with $\|A^Tc\|_1$ small.
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: Construction 3.13: edges $u \xrightarrow{a} v$, $v \xrightarrow{-a} u$ for each row $a$ and $v-u=a$ → edge occurrences $(i,\sigma,u)$ (row, sign, tail) with head $u+\sigma a_i\in(\mathbb Z_q^n)_l$; parallel edges kept; reason: with repeated rows or $q=2$ a set of pairs would merge edges that the count $\theta^{(n,l,k)}$ of Eq. (7) and $|E| = m\theta$ count separately; for distinct rows and $q\ne 2$ the two readings coincide
--   - reading: Construction 4.1: add $1$ to $c_i$ 'if $u_r-u_{r-1}=a_i$ for some $i$', else $-1$ if $=-a_i$ → $\pm1$ to $c_i$ for the recorded row $i$ and sign of the $r$-th edge; reason: the printed test is ambiguous when rows repeat or $a_i=-a_{i'}$; Theorem 4.12 uses the recorded labels, and for distinct rows with $q\ne2$ the two agree
--   - encoding: walk $W=(u_0,\dots,u_T)$ → start `u₀` and edges `p : Fin T → KEdge A l` with `IsWalk u₀ p`; $u_T$ = `walkVtx u₀ p (Fin.last T)`; reason: same object
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), pp. 14–15, Observations 4.2 and 4.3

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- Observations 4.2 and 4.3. Let `A ∈ Z_q^{m×n}` have rows with exactly `k` nonzero entries,
`⌈k/2⌉ ≤ l ≤ n`, and let `W = (u_0, …, u_T)` be a walk in `K_l(A)`. The vector `c` of
Construction 4.1 satisfies `‖c‖_1 ≤ T` and `A^T c = u_T − u_0`. -/
theorem observations_4_2_4_3 {m n q : ℕ} [NeZero q] (k l : ℕ)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (hA : HasKSparseRows k A)
    (hl₁ : (k + 1) / 2 ≤ l) (hl₂ : l ≤ n) (T : ℕ) (u₀ : KVert n q l) (p : Fin T → KEdge A l)
    (hp : (kikuchi A l).IsWalk u₀ p) :
    l1 (constrC p) ≤ T ∧
    A.transpose.mulVec (constrC p) =
      ((kikuchi A l).walkVtx u₀ p (Fin.last T)).val - u₀.val := by sorry

end SmallSecretLWE.Classical
