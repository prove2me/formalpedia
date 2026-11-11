-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_15
-- name    : SmallBiasPRF.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:35.468047+00:00
-- url     : https://prove2.me/theorems/e057c21a-07e0-45f8-ae01-61518e02ad50
-- title:
--   Lemma 15 — the weighted update operators have norm at most $1$
-- statement:
--   For every $B\subseteq A$ and every code coordinate $x\in\Omega$,
--
--   $$\|K_{B,x}\|_{op}\le1,\qquad \|K_B\|_{op}\le1 .$$
--
--   This is the uniform bound required by the operator amplification theorem (Theorem 32), applied to the inactive coordinates ($A_j=\emptyset$, where $K_{\emptyset,x}=Q_x$).
--
--   **Formalization Note** $B$ ranges over all subsets of $A$, including $\emptyset$ with $D_\emptyset=I$.
--
--   Differences from the source:
--   - generalization: A and {S_a} as in Theorem 6 and H of minimum relative distance at least 7/16 (standing in §5) → A any finite set of inputs and H any linear map; reason: the bound uses no property of A or H; the paper's setting is a special case
--   - encoding: operators on functions W → ℝ with the normalized inner product E_{S∈W}[f g]; operator norm ‖·‖_op → real matrices indexed by W, composition = matrix product, Euclidean L² operator norm (Matrix.Norms.L2Operator); reason: the normalized and Euclidean inner products differ by the constant |W|, so adjoints and operator norms coincide
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 15, p.23 (PDF 26)

import Mathlib
import Definitions.Def_SmallBiasPRF_KB

open scoped Matrix.Norms.L2Operator

namespace SmallBiasPRF

/-- **Lemma 15** (operator norms at most one), p.23 (PDF p.26).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 15, p.23 (PDF p.26).

For every `B ⊆ A` and `x ∈ Ω`, `‖K_{B,x}‖_op ≤ 1` and `‖K_B‖_op ≤ 1`.

**Formalization Note.** `B : Finset ↥A` is a subset of `A` (empty allowed, with `D_∅ = I`).
Operators are matrices indexed by `W` with the Euclidean operator norm. `A` and `H` are arbitrary
(the proof uses no property of them). -/
theorem lemma_15 (n m₁ : ℕ) [NeZero n] [NeZero m₁]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (A : Finset (Fin n → ZMod 2))
    (B : Finset A) (x : Fin m₁) :
    ‖KBx H A B x‖ ≤ 1 ∧ ‖KB H A B‖ ≤ 1 := by sorry

end SmallBiasPRF
