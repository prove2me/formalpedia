-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_best_response
-- name    : StrongWeakEq.Existence.best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:23.446802+00:00
-- url     : https://prove2.me/theorems/e9dec309-24cc-46eb-81f1-9046dc56bcb4
-- title:
--   Proof of Theorem 3.3, p. 26 — Φ has nonempty closed convex values in 𝒬 and is upper semicontinuous
-- statement:
--   Suppose every $D_i$ is nonempty, convex and compact, $f$ satisfies the standing assumptions (2.1)–(2.3), $q\mapsto f(t,i,q)$ is continuous on $D_i$ for every $t\ge0$, and $f(0,i,\cdot)$ is concave on $D_i$ for every $i$. Let
--   $$\Phi(Q)=\Big\{R\in\mathcal Q:\ R_i\in\arg\max_{q\in D_i}\big[f(0,i,q)+F(Q)\cdot q\big]\ \ \forall i\in S\Big\}.$$
--   Then:
--
--   1. for every $Q\in\mathcal Q$, $\Phi(Q)$ is a nonempty, closed, convex subset of $\mathcal Q$;
--   2. $\Phi$ is upper semicontinuous on $\mathcal Q$ in the sequential sense: if $Q^n\in\mathcal Q$, $Q\in\mathcal Q$, $Q^n\to Q$, $R^n\in\Phi(Q^n)$ and $R^n\to R$, then $R\in\Phi(Q)$.
--
--   These are the hypotheses of Kakutani–Fan's fixed-point theorem for $\Phi$ on the compact convex set $\mathcal Q$.
--
--   **Formalization Note** Nonemptiness of each $D_i$ and continuity of $q\mapsto f(t,i,q)$ on $D_i$ are added to the hypotheses of Theorem 3.3 (see the goal theorem); the paper's proof uses the continuity explicitly. Upper semicontinuity is stated with sequences, which is the characterization the paper itself uses on p. 26 and the form of Kakutani's theorem referenced in this mission. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 26, proof of Theorem 3.3 (properties of Φ)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_BestResponse

namespace StrongWeakEq.Existence

open Filter Topology

/-- Proof of Theorem 3.3, p. 26: for convex compact nonempty `Dᵢ`, `f(t,i,·)` continuous on `Dᵢ`
and `f(0,i,·)` concave, the best-response map `Φ` has nonempty, closed, convex values in `𝒬` and
is (sequentially) upper semicontinuous on `𝒬`. -/
theorem best_response {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f)
    (hne : ∀ i, (D i).Nonempty) (hconv : ∀ i, Convex ℝ (D i)) (hcpt : ∀ i, IsCompact (D i))
    (hcq : ∀ t, 0 ≤ t → ∀ i, ContinuousOn (f t i) (D i))
    (hconc : ∀ i, ConcaveOn ℝ (D i) (f 0 i)) :
    (∀ Q ∈ Controls D, (bestResponse D f Q).Nonempty ∧ IsClosed (bestResponse D f Q) ∧
        Convex ℝ (bestResponse D f Q) ∧ bestResponse D f Q ⊆ Controls D) ∧
    (∀ (Qn Rn : ℕ → Matrix (Fin N) (Fin N) ℝ) (Q R : Matrix (Fin N) (Fin N) ℝ),
      (∀ n, Qn n ∈ Controls D) → Q ∈ Controls D →
      Tendsto Qn atTop (𝓝 Q) → (∀ n, Rn n ∈ bestResponse D f (Qn n)) →
      Tendsto Rn atTop (𝓝 R) → R ∈ bestResponse D f Q) := by sorry

end StrongWeakEq.Existence
