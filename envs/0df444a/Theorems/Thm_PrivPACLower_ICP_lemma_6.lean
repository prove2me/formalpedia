-- Prove2me | Theorems.Thm_PrivPACLower_ICP_lemma_6
-- name    : PrivPACLower.ICP.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:47:55.856251+00:00
-- url     : https://prove2.me/theorems/c6ca733a-9298-457f-aff7-6b6872d25e80
-- title:
--   Lemma 6 — realizable blocks, padding and conditioned class costs
-- statement:
--   Let $0<\varepsilon\le1$, $0<\alpha_0\le1/4$ and $0\le\delta\le\alpha_0/8$. Suppose nonempty classes $G_i$ pack independently into $H$ via fixed maps $\Phi_i$, and write $s_i=m_{\rm priv}(G_i;\varepsilon,\delta,\alpha_0,1/4)$.
--
--   1. For every integer $1\le Q\le\sum_i(s_i-1)_+$, there exist integers $0\le q_i\le(s_i-1)_+$ with sum $Q$. Every choice of realizable blocks $S_i$ of sizes $q_i$ gives an $H$-realizable concatenation $\Phi_1(S_1)\cdots\Phi_k(S_k)$; zero-size blocks are empty.
--   2. Appending any number of copies of a padding point keeps each such database realizable.
--   3. For every component $j$ and $y\in Y_j$, at least one conditioned class $G_j^{(y,0)}$, $G_j^{(y,1)}$ is nonempty. Each nonempty conditioned class can replace $G_j$ with the same packing maps and has padding point $(\Phi_j(y),b)$. Some nonempty conditioned class also satisfies
--
--   $$m_{\rm priv}(G_j^{(y,b)};\varepsilon,\delta,\alpha_0/8,1/4)\ge\frac14\left(s_j-\frac{101}{\alpha_0\varepsilon}\right).$$
--
--   All five conclusion clauses appear in this item. They relate component costs without requiring the component domains to be finite.
--
--   Differences from the source:
--   - encoding: binary hypotheses, ordered databases and ordinary probabilities → Bool hypotheses, Fin-indexed databases, probability measures and extended nonnegative error probabilities; reason: retains replacement adjacency, improper outputs and the joint sample-and-learner experiment; all applied thresholds are nonnegative
--   - encoding: least sample size, possibly nonexistent → sInf in Nat-infinity with its infinity-preserving coercion into ENNReal; reason: unlearnable classes have infinite cost, zero-sample singleton classes retain cost zero, and infinite suprema are not replaced by zero
--   - reading: a distribution on a bare set with no sigma-algebra specified → a PMF, allowing arbitrary countable support; reason: uses the brief's discrete-law interpretation; on every finite domain this includes all distributions
--   - encoding: the real lower bound one quarter of s_j minus 101/(alpha_0 epsilon) → the same bound with extended nonnegative truncated subtraction; reason: negative right sides impose no constraint on a nonnegative cost; infinite s_j forces infinite conditioned cost
--   - generalization: (2): appending copies of a padding point to the database in (1) → (2) holds for every q with 0 ≤ qi ≤ (si − 1)+ and Σ qi = Q, not only for the integers produced by (1); reason: the integers of (1) are among those q; the proof of (2) does not depend on how they were chosen
-- source:
--   Prathamesh Dharangutte, Amartya Sanyal, STOC 2027 submission #366 (October 2026), p. 14, Lemma 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/366.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy
import Definitions.Def_PrivPACLower_ICP_Packing
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivPACLower.ICP

open PrivateUniformGen.Characterization


theorem lemma_6 {X : Type*} {k : ℕ} {Y : Fin k → Type*}
    (H : Set (X → Bool)) (Gs : ∀ i, Set (Y i → Bool)) (Φ : ∀ i, Y i → X)
    (hp : PackingVia H Gs Φ) (ε δ α₀ : ℝ)
    (hε : 0 < ε ∧ ε ≤ 1) (hα₀ : 0 < α₀ ∧ α₀ ≤ 1/4)
    (hδ : 0 ≤ δ ∧ δ ≤ α₀/8) :
    (∀ Q : ℕ, 1 ≤ Q → (Q : ℕ∞) ≤ blockCost Gs ε δ α₀ →
      ∃ q : Fin k → ℕ,
        (∀ i, (q i : ℕ∞) ≤ mpriv (Gs i) ε δ α₀ (1/4) - 1) ∧
        (∑ i, q i) = Q ∧
        ∀ S : ∀ i, Fin (q i) → Y i × Bool,
          (∀ i, 0 < q i → RealizableDB (Gs i) (S i)) →
            RealizableDB H (concatDB Φ q S)) ∧
    (∀ (Q : ℕ) (q : Fin k → ℕ), 1 ≤ Q →
      (∀ i, (q i : ℕ∞) ≤ mpriv (Gs i) ε δ α₀ (1/4) - 1) → (∑ i, q i) = Q →
      ∀ S : ∀ i, Fin (q i) → Y i × Bool,
        (∀ i, 0 < q i → RealizableDB (Gs i) (S i)) →
        ∀ z : X × Bool, PaddingPoint H Gs Φ z → ∀ r : ℕ,
          RealizableDB H (appendCopies (concatDB Φ q S) z r)) ∧
    (∀ (j : Fin k) (y : Y j),
      ((conditionedClass (Gs j) y false).Nonempty ∨
        (conditionedClass (Gs j) y true).Nonempty) ∧
      (∀ b : Bool, (conditionedClass (Gs j) y b).Nonempty →
        PackingVia H (restrictComponent Gs j y b) Φ ∧
        PaddingPoint H (restrictComponent Gs j y b) Φ (Φ j y,b)) ∧
      (∃ b : Bool, (conditionedClass (Gs j) y b).Nonempty ∧
        (1/4 : ℝ≥0∞) * (costReal (mpriv (Gs j) ε δ α₀ (1/4)) -
          ENNReal.ofReal (101/(α₀*ε))) ≤
            costReal (mpriv (conditionedClass (Gs j) y b) ε δ (α₀/8) (1/4)))) := by sorry

end PrivPACLower.ICP
