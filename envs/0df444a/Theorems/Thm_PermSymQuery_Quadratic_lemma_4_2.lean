-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_lemma_4_2
-- name    : PermSymQuery.Quadratic.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:24.96822+00:00
-- url     : https://prove2.me/theorems/bb6b0636-d2fe-4ba1-bbe6-8884ac72d057
-- title:
--   Lemma 4.2 — exact residual identity with unchanged query bound
-- statement:
--   Fix a natural upper bound $T\ge1$, and define $q=2T$, $K=10^8$ and $s=\min\{N,Kq^2\}$. For any string algorithm $\mathcal A$ with $T'\le T$ queries, any finite workspace and any Boolean output map, there are a rule $a_\mathcal A(S,z)\in[-1,1]$ and a residual algorithm $\mathcal R$ with $T''\le T$ queries and some finite workspace such that
--   $$h_\mathcal R(x\circ\pi)=h_\mathcal R(x)$$
--   for every string $x$ and position permutation $\pi$, and
--   $$\bar h_\mathcal A(x)=\mathbb E_{S:|S|=s}a_\mathcal A(S,x[S])+\frac18h_\mathcal R(x)$$
--   for every $x\in A^N$. The finite alphabet and injective binary encoding are arbitrary. The rule is bounded on every assignment to every sample. The sample size is computed from the original upper bound $T$, including when either algorithm uses fewer queries, and the case $s=N$ is included. This exact identity permits repeated residual constructions with the same query budget.
--
--   Differences from the source:
--   - encoding: positions [N], encoded bit strings, and signed Boolean outputs → Fin N, Fin b → ZMod 2, and true/false output probabilities; reason: these relabel the positions and binary registers and preserve the signed expectation Pr[1] − Pr[0]
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with a Boolean computational-basis output map and arbitrary finite workspace; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries
--   - encoding: a function of the labeled restriction x[S] and its uniform s-subset expectation → a dependent function on S and assignments S → A, averaged by the inverse binomial coefficient; reason: the rule cannot inspect any input value outside S and includes every source postprocessing rule
--   - encoding: s = N when N ≤ ceil(K(2T)^2), otherwise ceil(K(2T)^2) → s = min N (K * (2*T)^2); reason: K and T are natural numbers, so the ceiling is already equal to its integer argument
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 4.2, PDF p. 16 (printed p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

/-- Lemma 4.2, PDF p.16 (printed p.14). The original T chooses the sample even
when either algorithm uses fewer queries. Full-input sampling is included. -/
theorem lemma_4_2 {N b T T' : ℕ} {A W : Type} [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W] (enc : A → Bits b) (henc : Function.Injective enc)
    (hT : 1 ≤ T) (hT' : T' ≤ T)
    (alg : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) W T')
    (out : StateIndex N b W → Bool) :
    ∃ (a : Postprocess N (sampleSize N T) A) (m T'' : ℕ)
      (R : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) (Fin m) T'')
      (outR : StateIndex N b (Fin m) → Bool),
      BoundedPostprocess a ∧ T'' ≤ T ∧
      (∀ (x : Fin N → A) (π : Equiv.Perm (Fin N)),
        signed enc R outR (x ∘ π) = signed enc R outR x) ∧
      ∀ x : Fin N → A, symSigned enc alg out x =
        sampleAverage a x + (1 : ℝ) / 8 * signed enc R outR x := by sorry

end PermSymQuery.Quadratic
