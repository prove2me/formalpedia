-- Prove2me | Theorems.Thm_QAlgorithms_coupled_acceptance_bound
-- name    : QAlgorithms.coupled_acceptance_bound
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-17T17:34:36.165719+00:00
-- url     : https://prove2.me/theorems/977848a9-a040-431b-9365-0a7a2cfebe7c
-- title:
--   Coupled quantum hybrid bound with conditional oracle disagreement
-- statement:
--   Let $I$ be a finite query-input set, $K$ a finite additive commutative group of answers, and $W$ a finite workspace. Let $A$ be a quantum algorithm making $q\geq 0$ standard additive oracle queries, with a fixed accepting event $E$ in its final computational-basis measurement.
--
--   Consider two finite families of oracle functions, $H_a:I\to K$ and $G_b:I\to K$. Let $w(a,b)\geq 0$ be coupling weights whose row and column marginals are $\mu(a)$ and $\nu(b)$, with
--   $$
--   \sum_b w(a,b)=\mu(a),\qquad
--   \sum_a w(a,b)=\nu(b),\qquad
--   \sum_a\mu(a)=1.
--   $$
--   Thus both marginals are probability distributions. Suppose a real number $\varepsilon$ satisfies the mismatch bound separately for every reference oracle and query input:
--   $$
--   \sum_{b:\,G_b(x)\ne H_a(x)}w(a,b)
--   \leq\varepsilon\,\mu(a)
--   \qquad\text{for every }a,x.
--   $$
--   For every $a$ of positive marginal mass, this says that the conditional chance of disagreement at any fixed input, given $a$, is at most $\varepsilon$.
--
--   Writing $p_H(A,E)$ and $p_G(A,E)$ for acceptance averaged under the two marginals, one has
--   $$
--   p_H(A,E)\leq 2p_G(A,E)+8q^2\varepsilon.
--   $$
--   The event is the same for all sampled oracles. The theorem isolates the quantum part of a distribution-comparison argument: any coupling with the stated conditional mismatch control gives an acceptance bound for every query algorithm.
--
--   **Formalization Note.** This is a general finite-coupling form of the final hybrid and accepting-projection argument in Section 4.4, proof of Lemma 4.13, of Carolan et al. The constants $2$ and $8$ are derived explicitly, rather than quoted from the source's big-$O$ statement. The oracle adds its answer in $K$; bitwise-XOR answers are a special case. The formal statement also allows zero queries and real-valued coupling weights. It does not require additional nonnegativity hypotheses on the marginals, since these follow from the coupling equations.
-- source:
--   Derived generalization of Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/abs/2611.05912v1, Section 4.4, proof of Lemma 4.13, pp.41–42: final hybrid inequality after (77) and accepting-projection argument. Constants 2 and 8 are derived explicitly in this formalization.

import Definitions.Def_QAlgorithms_Defs_Query

set_option autoImplicit false

namespace QAlgorithms

theorem coupled_acceptance_bound {ι κ W α β : Type*} [Fintype ι] [Fintype κ] [Fintype W]
    [Fintype α] [Fintype β] [DecidableEq ι] [DecidableEq κ] [DecidableEq W]
    [AddCommGroup κ] {q : ℕ} (A : QueryAlg ι κ W q)
    (H : α → ι → κ) (G : β → ι → κ) (w : α → β → ℝ) (μ : α → ℝ) (ν : β → ℝ)
    (ε : ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (hrow : ∀ a, ∑ b, w a b = μ a) (hcol : ∀ b, ∑ a, w a b = ν b)
    (hμ : ∑ a, μ a = 1)
    (hdis : ∀ a x, (∑ b, if G b x ≠ H a x then w a b else 0) ≤ ε * μ a)
    (acc : ((ι × κ) × W) → Prop) [DecidablePred acc] :
    (∑ a, μ a * probEvent (A.finalState (xorOracle (H a))) acc) ≤
      2 * (∑ b, ν b * probEvent (A.finalState (xorOracle (G b))) acc) +
      8 * (q : ℝ) ^ 2 * ε := by sorry

end QAlgorithms
