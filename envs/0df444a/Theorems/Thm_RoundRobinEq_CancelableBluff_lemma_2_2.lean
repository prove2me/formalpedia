-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableBluff_lemma_2_2
-- name    : RoundRobinEq.CancelableBluff.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:16.923449+00:00
-- url     : https://prove2.me/theorems/2627545c-43ca-4f42-b33d-a7cc147f11e7
-- title:
--   Lemma 2.2 — cancelability extends from a single good to any set disjoint from S ∪ T
-- statement:
--   Let $v : 2^M \to \mathbb R$ be cancelable, and let $S, T, R \subseteq M$ with $R \cap (S \cup T) = \emptyset$. Then
--
--   1. $v(S \cup R) > v(T \cup R) \;\Longrightarrow\; v(S) > v(T)$;
--   2. $v(S) \ge v(T) \;\Longrightarrow\; v(S \cup R) \ge v(T \cup R)$;
--   3. $v(S) = v(T) \;\Longrightarrow\; v(S \cup R) = v(T \cup R)$.
--
--   $$
--   v(S \cup R) > v(T \cup R) \Rightarrow v(S) > v(T), \qquad v(S) \ge v(T) \Rightarrow v(S \cup R) \ge v(T \cup R).
--   $$
--
--   Cancelability is defined by adding one good; the lemma says that adding a whole set of fresh goods to both sides never reverses a comparison. It is the tool behind Lemma 3.3 and the observation that, for cancelable valuations, a good of largest singleton value also has the largest marginal value.
--
--   **Formalization Note** The page reads "$R \subseteq M \setminus S \cup T$", which means $R \subseteq M \setminus (S \cup T)$; it is stated as `Disjoint R (S ∪ T)`. The page writes $v_i$ for $v$ inside the statement. The lemma assumes only cancelability: the page's codomain $\mathbb R_{\ge 0}$ and the standing monotonicity are not used, so the Lean statement takes any real-valued cancelable $v$ (a statement at least as strong as the page's).
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 5, Lemma 2.2

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.CancelableBluff

theorem lemma_2_2 {M : Type*} [DecidableEq M] (v : Finset M → ℝ) (hv : IsCancelable v)
    (S T R : Finset M) (hR : Disjoint R (S ∪ T)) :
    (v (T ∪ R) < v (S ∪ R) → v T < v S) ∧
      (v T ≤ v S → v (T ∪ R) ≤ v (S ∪ R)) ∧
      (v S = v T → v (S ∪ R) = v (T ∪ R)) := by sorry

end RoundRobinEq.CancelableBluff
