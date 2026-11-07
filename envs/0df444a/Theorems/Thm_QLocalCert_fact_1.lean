-- Prove2me | Theorems.Thm_QLocalCert_fact_1
-- name    : QLocalCert.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:32.060328+00:00
-- url     : https://prove2.me/theorems/30afd28f-36a2-4854-8bf1-60bbc48215aa
-- title:
--   Fact 1 — $T^{\mathrm{tr}}_{N,\mu}(z,z')$ is a tree of order $n_\mu(N)=\Theta(N\log^2N)+2\mu$
-- statement:
--   1. For every $\mu\ge1$, every even $N\ge8$ and all balanced $z,z'\in\{0,1\}^N$, the graph $T^{\mathrm{tr}}_{N,\mu}(z,z')$ is a tree with exactly $n_\mu(N)$ vertices, where
--   $$
--   n_\mu(N)=2\Big[1+m+(m+1)(3+B_L)+2\sum_{i=0}^m\mathrm{wt}(i)\Big]+2\mu,\qquad m=\tfrac N2,\ B_L=\tfrac{L(L+1)}2 ;
--   $$
--   in particular the order depends only on $N$ (and $\mu$), not on $(z,z')$.
--   2. For fixed $\mu\ge1$, $n_\mu(N)$ is strictly increasing over even $N\ge8$.
--   3. There are constants $c_1,c_2>0$, independent of $\mu$, with
--   $$
--   c_1N\log_2^2N\le n_\mu(N)-2\mu\le c_2N\log_2^2N\qquad(\mu\ge1,\ N\ge8\text{ even}).
--   $$
--
--   These facts fix the instance sizes of the lower bound and let Theorem 29 translate $b=\Omega(N/\mu)$ into $\Omega(n/(\mu\log^2n))$.
--
--   Differences from the source:
--   - encoding: order n_µ(N) = Θ(N log² N) + 2µ with constants independent of µ; depends only on N → card = order µ N (the exact count of the proof) and c₁, c₂ > 0 before µ and N bounding order µ N − 2µ; reason: Θ as explicit constants; dependence only on N is the exact formula
--   - encoding: strictly increasing in N → order µ N < order µ N' for even 8 ≤ N < N'; reason: the statement concerns the even N ≥ 8 of §4
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Fact 1 and its proof, p.35

import Mathlib
import Definitions.Def_QLocalCert_Ttr
import Definitions.Def_QLocalCert_order

set_option autoImplicit false

namespace QLocalCert

/-- **Fact 1** (p.35). "For every positive integer µ, every even N ≥ 8, and z, z′ ∈ {0, 1}^N of
Hamming weight N/2, the graph T^tr_{N,µ}(z, z′) is a tree. Its order is n_µ(N) = Θ(N log² N) + 2µ,
with constants independent of µ. For fixed µ, this order depends only on N, not on (z, z′), and is
strictly increasing in N."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Fact 1 and its proof, p.35.

**Formalization Note.** Three clauses: (1) the tree property and the exact order
`|V(T^tr_{N,µ}(z, z′))| = order µ N` (the count of the proof, which does not involve `z, z′`);
(2) `order µ N` is strictly increasing over even `N ≥ 8`; (3) `Θ(N log² N)` with constants
`c₁, c₂ > 0` chosen before `µ` and `N`: `c₁ N log₂² N ≤ n_µ(N) − 2µ ≤ c₂ N log₂² N`. -/
theorem fact_1 :
    (∀ μ N : ℕ, 1 ≤ μ → Even N → 8 ≤ N → ∀ z z' : Fin N → Bool, Balanced z → Balanced z' →
      (Ttr N μ z z').IsTree ∧
        Fintype.card (TV N μ (runLengths z) (runLengths z')) = order μ N) ∧
    (∀ μ N N' : ℕ, 1 ≤ μ → Even N → Even N' → 8 ≤ N → N < N' → order μ N < order μ N') ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ μ N : ℕ, 1 ≤ μ → Even N → 8 ≤ N →
      c₁ * N * Real.logb 2 N ^ 2 ≤ (order μ N : ℝ) - 2 * μ ∧
        (order μ N : ℝ) - 2 * μ ≤ c₂ * N * Real.logb 2 N ^ 2) := by sorry

end QLocalCert
