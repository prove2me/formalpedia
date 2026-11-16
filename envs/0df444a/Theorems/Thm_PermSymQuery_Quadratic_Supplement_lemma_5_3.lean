-- Prove2me | Theorems.Thm_PermSymQuery_Quadratic_Supplement_lemma_5_3
-- name    : PermSymQuery.Quadratic.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:39:55.655575+00:00
-- url     : https://prove2.me/theorems/c9c95551-6d25-4f3d-9a0c-a7936a8e5050
-- title:
--   Lemma 5.3 — exact residual identity for hypergraph algorithms
-- statement:
--   Fix $k\ge2$ and $T\ge1$, let $K=10^8$ and $s=K(2kT)^2$, and assume $N>s$. Let $\mathcal A$ be any quantum algorithm making $T'\le T$ queries to the ordered-tuple hypergraph oracle on $[N]$, with any finite workspace and any Boolean output map. Then there are a postprocessing rule $a_{\mathcal A}(S,Z)\in[-1,1]$ and an algorithm $R(\mathcal A)$ making $T''\le T$ hypergraph queries, with some finite workspace, such that $R(\mathcal A)$ is symmetrized,
--   $$h_{R(\mathcal A)}(H^\pi)=h_{R(\mathcal A)}(H)\qquad\text{for every hypergraph }H\text{ and every }\pi\in S_N,$$
--   and, for every $k$-uniform hypergraph $H$ on $[N]$,
--   $$\bar h_{\mathcal A}(H)=\mathbb E_S\,a_{\mathcal A}(S,H[S])+\lambda\,h_{R(\mathcal A)}(H),\qquad\lambda=\frac18 .$$
--   Here $S$ is uniform among the $s$-element vertex subsets of $[N]$, and the rule sees only $S$ and the induced hypergraph $H[S]$. The sample size is fixed by the original bound $T$, even when either algorithm uses fewer queries. The identity holds exactly and for every hypergraph, not only on a promise.
--
--   This is the hypergraph residual identity that Proposition 5.4 iterates with the same query budget.
--
--   Differences from the source:
--   - encoding: vertex set [N], ordered vertex tuples, one answer bit and signed outputs → Fin N, Fin k → Fin N, ZMod 2, and output probabilities of true and false; reason: these relabel the vertices and registers and preserve the signed expectation Pr[1] − Pr[0]
--   - encoding: arbitrary finite quantum workspaces and two-outcome measurements → published QueryAlg with an arbitrary finite workspace and a Boolean computational-basis output map; reason: input-independent final unitaries and ancillary registers realize every source measurement without additional queries (the base mission's convention)
--   - encoding: a function a_A(S, H[S]) ∈ [−1, 1] and E_S over uniform s-element subsets → a dependent function on samples S and hypergraphs on S, bounded on every argument, averaged by the inverse binomial coefficient; reason: the rule cannot read any hyperedge outside S and includes every source postprocessing rule
--   - encoding: N > ⌈K(2kT)²⌉ and s = ⌈K(2kT)²⌉ → hSampleSize k T = K * (2*k*T)^2 < N, with s = hSampleSize k T; reason: K, k and T are natural numbers, so the ceiling equals its argument
--   - reading: a symmetrized algorithm R(A) → an algorithm whose signed expectation satisfies h_R(H^π) = h_R(H) for all H and π; reason: running R0(A) on H^τ for uniform τ makes the signed expectation relabeling-invariant, which is the property the iteration uses; the published base Lemma 4.2 uses the same reading
-- source:
--   Yunqi Huang, Lvzhou Li, Zekun Ye, Shenggen Zheng, Optimal Separations Between Randomized and Quantum Query Complexity under Permutation Symmetry, STOC 2027 submission #1644 (October 2026), Lemma 5.3, PDF p. 23 (printed p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1644.pdf

import Mathlib
import Definitions.Def_PermSymQuery_Quadratic_Supplement_Hypergraph

namespace PermSymQuery.Quadratic.Supplement

/-- Lemma 5.3, PDF p.23 (printed p.21). `s = K(2kT)²` is fixed by the original bound `T` even
when either algorithm uses fewer queries; the identity holds for every hypergraph. -/
theorem lemma_5_3 {k N T T' : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (hk : 2 ≤ k) (hT : 1 ≤ T) (hN : hSampleSize k T < N) (hT' : T' ≤ T)
    (alg : QAlgorithms.QueryAlg (Fin k → Fin N) (ZMod 2) W T')
    (out : HStateIndex N k W → Bool) :
    ∃ (a : HPostprocess N (hSampleSize k T) k) (m T'' : ℕ)
      (R : QAlgorithms.QueryAlg (Fin k → Fin N) (ZMod 2) (Fin m) T'')
      (outR : HStateIndex N k (Fin m) → Bool),
      HBounded a ∧ T'' ≤ T ∧
      (∀ (H : Hypergraph (Fin N) k) (π : Equiv.Perm (Fin N)),
        hSigned R outR (relabel H π) = hSigned R outR H) ∧
      ∀ H : Hypergraph (Fin N) k, hSymSigned alg out H =
        hSampleAverage a H + (1 : ℝ) / 8 * hSigned R outR H := by sorry

end PermSymQuery.Quadratic.Supplement
