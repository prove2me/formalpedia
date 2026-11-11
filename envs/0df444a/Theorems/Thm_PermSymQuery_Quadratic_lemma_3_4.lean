-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_lemma_3_4
-- name    : PermSymQuery.Quadratic.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:09.100405+00:00
-- url     : https://prove2.me/theorems/fa58a32d-773c-4aae-9b18-ac4b3d76d22c
-- title:
--   Lemma 3.4 — approximation from the sampled input
-- statement:
--   Let $A$ be any finite alphabet, $\mathrm{enc}:A\to\{0,1\}^b$ any injective encoding, and $\mathcal A$ any $T$-query string algorithm with any finite workspace and Boolean output map. Put $q=2T\ge1$. Assume $q+1<s<N$ and $3q+2\le N$. There is a rule $a_\mathcal A(S,z)\in[-1,1]$ for every $s$-element sample $S$ and assignment $z:S\to A$ such that, for every string $x\in A^N$,
--   $$\left|\bar h_\mathcal A(x)-\ell_\mathcal A(x)\right|\le2q\eta_{N,s,q},\qquad\ell_\mathcal A(x)=\mathbb E_{S:|S|=s}a_\mathcal A(S,x[S]).$$
--   The signed expectation is the probability of output one minus the probability of output zero, and the bar averages position permutations. No promise restriction is imposed on this conclusion. The rule uses only the labeled sample, making this an approximation available to a classical sampling simulator.
--
--   Differences from the source:
--   - encoding: positions [N], encoded bit strings, and signed Boolean outputs → Fin N, Fin b → ZMod 2, and true/false output probabilities; reason: these relabel the positions and binary registers and preserve the signed expectation Pr[1] − Pr[0]
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with a Boolean computational-basis output map and arbitrary finite workspace; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries
--   - encoding: a function of the labeled restriction x[S] and its uniform s-subset expectation → a dependent function on S and assignments S → A, averaged by the inverse binomial coefficient; reason: the rule cannot inspect any input value outside S and includes every source postprocessing rule
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 3.4, PDF p. 13 (printed p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Model

namespace PermSymQuery.Quadratic

/-- Lemma 3.4, PDF p.13 (printed p.11): all inputs, and all bounded local assignments. -/
theorem lemma_3_4 {N b T s : ℕ} {A W : Type} [Fintype A] [DecidableEq A]
    [Fintype W] [DecidableEq W] (enc : A → Bits b) (henc : Function.Injective enc)
    (alg : QAlgorithms.QueryAlg (Option (Fin N)) (Bits b) W T)
    (out : StateIndex N b W → Bool) (hT : 1 ≤ 2 * T)
    (hs : 2 * T + 1 < s) (hsN : s < N) (hN : 3 * (2 * T) + 2 ≤ N) :
    ∃ a : Postprocess N s A, BoundedPostprocess a ∧
      ∀ x : Fin N → A, |symSigned enc alg out x - sampleAverage a x| ≤
        2 * (2 * T : ℕ) * eta N s (2 * T) := by sorry

end PermSymQuery.Quadratic
