-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_16
-- name    : SmallBiasPRF.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:03.875199+00:00
-- url     : https://prove2.me/theorems/73f28d47-ae08-4378-819d-1d2b9951f5ff
-- title:
--   Lemma 16 — $\|K_B\|_{op}\le 95/96$ for every nonempty active set
-- statement:
--   Let $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ be a linear code of minimum relative distance at least $7/16$ and $A\subseteq\{0,1\}^n$. For every nonempty $B\subseteq A$,
--
--   $$\|K_B\|_{op}\le\frac{95}{96}.$$
--
--   This is the main operator lemma: on every active coordinate the averaged weighted update contracts by a constant factor, independent of $n$, $m_1$ and $B$.
--
--   **Formalization Note** The proof (§5.10) is a weighted Schur test with weight $\Psi_B$; it is not part of the statement.
--
--   Differences from the source:
--   - generalization: A and {S_a} as in Theorem 6 (A nonempty, |S_a| ≥ 4096(n + m₁)) → A any finite set of inputs; no family {S_a}; reason: K_B depends only on H, A and B, and the proof uses no property of A beyond B ⊆ A; nonemptiness of A follows from that of B
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
--   - encoding: operators on functions W → ℝ with the normalized inner product E_{S∈W}[f g]; operator norm ‖·‖_op → real matrices indexed by W, composition = matrix product, Euclidean L² operator norm (Matrix.Norms.L2Operator); reason: the normalized and Euclidean inner products differ by the constant |W|, so adjoints and operator norms coincide
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 16, p.23 (PDF 26); proof §5.10, pp.35–36 (PDF 38–39)

import Mathlib
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_KB

open scoped Matrix.Norms.L2Operator

namespace SmallBiasPRF

/-- **Lemma 16** (contraction for every active set), p.23 (PDF p.26); proved in §5.10, pp.35–36.
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 16, p.23 (PDF p.26).

For every nonempty `B ⊆ A`, `‖K_B‖_op ≤ 95/96`, where `H` is a linear code of minimum relative
distance at least `7/16` (the standing assumption of §5, from Theorem 6).

**Formalization Note.** `A` is any finite set of inputs; the paper's further standing assumptions
on `A` (nonempty, which `B` already forces) and on `{S_a}` (not involved in `K_B`) are not
needed. Operators are matrices indexed by `W` with the Euclidean operator norm. -/
theorem lemma_16 (n m₁ : ℕ) [NeZero n] [NeZero m₁]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16))
    (A : Finset (Fin n → ZMod 2)) (B : Finset A) (hB : B.Nonempty) :
    ‖KB H A B‖ ≤ 95 / 96 := by sorry

end SmallBiasPRF
