-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_Supplement_lemma_6_1
-- name    : PermSymQuery.Quadratic.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:41:56.192815+00:00
-- url     : https://prove2.me/theorems/ef99c110-6e47-4187-acc2-b4efa20b4381
-- title:
--   Lemma 6.1 — structural recovery of the encoding $H_z$
-- statement:
--   Fix $k\ge2$. There are $b_0$ and $\gamma_k>0$ such that for every $b\ge b_0$ there is a threshold $\tau$, depending only on $k$ and $b$, with the following properties. Let $d=2^b-1$, let $m\le\binom{2^{b-2}}k$, let $e:[m]\to\binom{X^*}k$ be any injective enumeration of $k$-subsets of $X^*$, and let $z,z'\in\{0,1\}^m$. Then, for the hypergraph $H_z$ of (23):
--   1. $H_z$ is connected (its incidence graph is connected);
--   2. $\deg(x)\le\tau-\gamma_kd^{k-1}$ for every data vertex $x\in X$;
--   3. $\deg(a)\ge\tau+\gamma_kd^{k-1}$ for every address vertex $a\in A$;
--   4. the hypergraph identifies every $a_i$ and every address: every vertex bijection $\sigma$ with $H_{z'}(\sigma(E))=H_z(E)$ for all $E$ fixes every vertex;
--   5. $$H_z\cong H_{z'}\iff z=z'.$$
--
--   This lemma makes the promise problem $F_g$ of §6.2 well defined and permutation-invariant, with a promise of connected hypergraphs.
--
--   Differences from the source:
--   - generalization: e enumerates the first m k-subsets of X* in lexicographic order of binary address → e is any injective map from Fin m to k-subsets of X*; reason: the lexicographic enumeration is one such map (the paper does not fix which address bit is most significant, and nothing depends on the order), so the Lean statement specializes to the source
--   - encoding: vertices x_w (w ∈ {0,1}^b \ {0^b}) and a_1, …, a_b, with 1-based address bits → EncV b = EncX b ⊕ Fin b, with Sum.inr i standing for a_{i+1} and bit w i for w_{i+1}; reason: a relabeling of the vertex set and of the bit indices
--   - reading: the hypergraph uniquely identifies every a_i and every address in X → every vertex bijection σ with H_{z'}(σ(E)) = H_z(E) for all E is the identity; reason: the proof shows that an isomorphism preserves the vertex classes and the ordered address vertices and sends each x_w to the vertex with the same address
--   - encoding: for sufficiently large b0(k); τ determined only by k and b; γ_k > 0 → ∃ b0, ∃ γ > 0 after k, ∀ b ≥ b0, ∃ τ before m, e, z and z'; reason: this is the stated dependence of the constants
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 6.1, PDF p. 26 (printed p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Encoding

namespace PermSymQuery.Quadratic.Supplement

/-- Lemma 6.1, PDF p.26 (printed p.24). `γ` depends only on `k`, `τ` only on `k` and `b`;
`d = 2^b − 1`. The data positions `e` may be any injective enumeration of k-subsets of `X*`.
"Uniquely identifies every `a_i` and every address" is the clause that every vertex bijection
carrying `H_z` to `H_{z'}` is the identity. -/
theorem lemma_6_1 : ∀ k : ℕ, 2 ≤ k → ∃ b0 : ℕ, ∃ γ : ℝ, 0 < γ ∧
    ∀ b : ℕ, b0 ≤ b → ∃ τ : ℝ,
    ∀ (m : ℕ), m ≤ Nat.choose (2 ^ (b - 2)) k →
    ∀ (e : Fin m → KSet (EncV b) k), IsDataEnumeration e →
    ∀ z : Fin m → Bool,
      HConnected (Hz e z) ∧
      (∀ x : EncX b,
        (hdeg (Hz e z) (Sum.inl x) : ℝ) ≤ τ - γ * ((2 : ℝ) ^ b - 1) ^ (k - 1)) ∧
      (∀ i : Fin b,
        τ + γ * ((2 : ℝ) ^ b - 1) ^ (k - 1) ≤ (hdeg (Hz e z) (Sum.inr i) : ℝ)) ∧
      (∀ (z' : Fin m → Bool) (σ : Equiv.Perm (EncV b)),
        (∀ E : KSet (EncV b) k, Hz e z' (KSet.map σ E) = Hz e z E) → ∀ v, σ v = v) ∧
      (∀ z' : Fin m → Bool, HIso (Hz e z) (Hz e z') ↔ z = z') := by sorry

end PermSymQuery.Quadratic.Supplement
