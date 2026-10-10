-- Prove2me | Theorems.Thm_StrongWeakEq_Existence_theorem_3_3
-- name    : StrongWeakEq.Existence.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:48.514208+00:00
-- url     : https://prove2.me/theorems/e0a8d0d3-d248-4197-9ceb-e707cafd5892
-- title:
--   Theorem 3.3, p. 10 — weak equilibria exist for convex compact Dᵢ and concave f(0,i,·); strong ones under strict concavity and Lemma 3.2
-- statement:
--   Let $S=\{1,\dots,N\}$ and suppose that, for every $i\in S$, the admissible set $D_i\subseteq E_i$ of (2.1) is nonempty, convex and compact. Let $f$ satisfy the standing assumptions (2.2)–(2.3), let $q\mapsto f(t,i,q)$ be continuous on $D_i$ for all $t\ge0$ and $i\in S$, and let $f(0,i,\cdot)$ be concave on $D_i$ for all $i\in S$. Then:
--
--   1. there exists a weak equilibrium $Q^*\in\mathcal Q$;
--   2. if moreover $f(0,i,\cdot)$ is strictly concave on $D_i$ for all $i\in S$ and $f$ satisfies the conditions of Lemma 3.2 (for a time derivative $f_t$ of $f$), there exists a strong equilibrium $Q^*\in\mathcal Q$.
--
--   In short,
--   $$D_i \text{ convex compact},\ f(0,i,\cdot)\text{ concave}\ \Longrightarrow\ \exists\,Q^*\ \text{weak};\qquad +\ \text{strict concavity and Lemma 3.2}\ \Longrightarrow\ \exists\,Q^*\ \text{strong}.$$
--
--   This is the paper's general existence result: the case-by-case machinery of Theorem 3.1 and Proposition 3.2 does not say a priori whether an equilibrium exists, and Remark 3.4 shows that without compactness none may exist.
--
--   **Formalization Note** Two hypotheses are added to the printed statement. (i) Continuity of $q\mapsto f(t,i,q)$ on $D_i$: the paper's proof uses the continuity of $q\mapsto f(0,i,q)+F(Q)\cdot q$ and of $Q\mapsto F(Q)$, and the statement is false without it (with $N=2$, $D_1=\{(-a,a):a\in[0,1]\}$, $D_2=\{(0,0)\}$ and $f(t,1,(-a,a))=te^{-t}s(a)$ for a sign $s$ switching at $a=\tfrac12$, no row satisfies (3.10)). (ii) $D_i\neq\emptyset$: otherwise $\mathcal Q=\emptyset$. The shift bound (3.3) is not assumed in part 1; the paper's proof cites Theorem 3.1, which assumes it, but the statement holds without it. The expectation $\mathbb E_{i,Q}$ over the chain is written out through its one-dimensional marginals: under a generator $Q$ the law of $X_t$ given $X_0=i$ is the $i$-th row of the matrix exponential $e^{tQ}$, so $\mathbb E_{i,Q}[\int_0^\infty \varphi(t,X_t)\,dt]=\int_0^\infty\sum_j (e^{tQ})_{ij}\varphi(t,j)\,dt$ by Fubini; no Markov process is constructed.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 10, Theorem 3.3 (proof pp. 26, Appendix A.4)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.Existence

/-- Theorem 3.3, p. 10: if every `Dᵢ` is nonempty, convex and compact, `f` satisfies (2.2)–(2.3),
`q ↦ f(t,i,q)` is continuous on `Dᵢ` and `f(0,i,·)` is concave, a weak equilibrium exists; if
moreover `f(0,i,·)` is strictly concave and `f` satisfies the conditions of Lemma 3.2, a strong
equilibrium exists. -/
theorem theorem_3_3 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : Standing D f)
    (hne : ∀ i, (D i).Nonempty) (hconv : ∀ i, Convex ℝ (D i)) (hcpt : ∀ i, IsCompact (D i))
    (hcq : ∀ t, 0 ≤ t → ∀ i, ContinuousOn (f t i) (D i))
    (hconc : ∀ i, ConcaveOn ℝ (D i) (f 0 i)) :
    (∃ Qs, IsWeakEquilibrium D f Qs) ∧
    (∀ ft : ℝ → Fin N → (Fin N → ℝ) → ℝ, (∀ i, StrictConcaveOn ℝ (D i) (f 0 i)) →
      SecondOrderReg D f ft → ∃ Qs, IsStrongEquilibrium D f Qs) := by sorry

end StrongWeakEq.Existence
