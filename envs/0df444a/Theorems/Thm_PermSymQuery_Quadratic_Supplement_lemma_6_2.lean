-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_Supplement_lemma_6_2
-- name    : PermSymQuery.Quadratic.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:42:37.214766+00:00
-- url     : https://prove2.me/theorems/5044e50c-50e5-4b45-92d3-15d6482612b7
-- title:
--   Lemma 6.2 — classical reduction $R_\varepsilon(F_g)\ge R_\varepsilon(g)$
-- statement:
--   Fix $k\ge2$. There is $b_0$ such that the following holds for every $b\ge b_0$. Let $m\le\binom{2^{b-2}}k$, let $e:[m]\to\binom{X^*}k$ be any injective enumeration of $k$-subsets of $X^*$, let $\sigma$ be any identification of the vertex set $V=X\cup A$ with $[N]$, and let $g:D_g\subseteq\{0,1\}^m\to\{0,1\}$ be nonconstant on $D_g$. Then for every $0<\varepsilon<1/2$,
--   $$R_\varepsilon(F_g)\ge R_\varepsilon(g).$$
--   Here $R_\varepsilon(g)$ is the randomized query complexity of $g$ with bit queries, and $R_\varepsilon(F_g)$ the randomized hyperedge-membership query complexity of the hypergraph property $F_g$ on its promise $D_{F_g}=\{H_z^\pi:z\in D_g,\ \pi\in S_N\}$, both with worst-case cost and error at most $\varepsilon$ on every promised input.
--
--   This is the lower-bound half of the hypergraph encoding used for Theorem 1.3.
--
--   Differences from the source:
--   - generalization: e enumerates the first m k-subsets of X* in lexicographic order of binary address → e is any injective map from Fin m to k-subsets of X*; reason: the lexicographic enumeration is one such map (the paper does not fix which address bit is most significant, and nothing depends on the order), so the Lean statement specializes to the source
--   - encoding: vertices x_w (w ∈ {0,1}^b \ {0^b}) and a_1, …, a_b, with 1-based address bits → EncV b = EncX b ⊕ Fin b, with Sum.inr i standing for a_{i+1} and bit w i for w_{i+1}; reason: a relabeling of the vertex set and of the bit indices
--   - generalization: the canonical vertex set identified with [N] by one fixed labeling → any bijection σ : V ≃ Fin N; reason: the fixed identification is one such bijection, so the statement specializes to the source
--   - reading: b ≥ b0(k), with b0(k) ≥ 7 chosen sufficiently large in §6.1 → ∃ b0, ∀ b ≥ b0; reason: §6.1 and Lemma 6.1 specify b0(k) only as sufficiently large
--   - encoding: F_g(H_z^π) = g(z) on D_{F_g} → Fg H = 1 iff H = H_z^π for some z ∈ D_g and π with g(z) = 1; reason: by Lemma 6.1 the two agree on the promise; values outside the promise are never read
--   - encoding: R_ε(g) for a partial Boolean function g on m bits → the base mission's Reps with N := m and A := Bool; reason: one query reads one bit z_j
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 6.2, PDF p. 27 (printed p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Encoding

namespace PermSymQuery.Quadratic.Supplement

/-- Lemma 6.2, PDF p.27 (printed p.25): `R_ε(F_g) ≥ R_ε(g)` for nonconstant `g`,
`b ≥ b0(k)`, `m ≤ (2^{b−2} choose k)` and `0 < ε < 1/2`. `R_ε(g)` is the base string-model
`Reps` with `N := m`, `A := Bool`; the identification `σ` of `V` with `[N]` is arbitrary. -/
theorem lemma_6_2 : ∀ k : ℕ, 2 ≤ k → ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
    ∀ (m : ℕ), m ≤ Nat.choose (2 ^ (b - 2)) k →
    ∀ (e : Fin m → KSet (EncV b) k), IsDataEnumeration e →
    ∀ (N : ℕ) (σ : EncV b ≃ Fin N) (Dg : Set (Fin m → Bool)) (g : (Fin m → Bool) → Bool),
      (∃ z ∈ Dg, ∃ z' ∈ Dg, g z ≠ g z') →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      PermSymQuery.Quadratic.Reps Dg g ε ≤ HReps (FgDomain σ e Dg) (Fg σ e Dg g) ε := by sorry

end PermSymQuery.Quadratic.Supplement
