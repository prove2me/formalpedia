-- Prove2me | Theorems.Thm_SharpConsist_lemma_5_3
-- name    : SharpConsist.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:16.980527+00:00
-- url     : https://prove2.me/theorems/1a8575ac-6295-495c-a5c2-c03d526c28db
-- title:
--   Lemma 5.3 — transcript hiding, for each random tape
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, integers $k\ge1$, $n=(m+1)k$, $Q\ge0$, and $\delta=1/(64m)$. Let $P$ be a deterministic adaptive rule that makes $Q$ value queries on subsets of $X=[n]$ and then outputs a subset of $X$ — the pre-arrival phase of an algorithm whose random tape is fixed. Then at least a
--   $$1-2(Q+1)e^{-\delta^2k/2}$$
--   fraction of the $k$-subsets $A\subseteq X$ satisfy all of:
--
--   1. the answers $P$ receives from $f_A$ coincide with those it receives from the reference instance $f_{\mathrm{ref}}$ of Eq. (5.10);
--   2. the output of $P$ against $f_A$ equals its output against $f_{\mathrm{ref}}$;
--   3. that output $S$ has imbalance $|u_A(S)|\le\delta$.
--
--   Averaging over the tape gives the paper's statement: with probability at least $1-2(Q+1)e^{-\delta^2k/2}$ over $A$ and the algorithm's randomness, its answers and output before $r$ agree with a reference execution against $\psi$, and that output is balanced.
--
--   **Formalization Note.** The rule is `NonmonotoneSubmod.QueryLB.DetAlg (Fin n) Q`; the answers are compared as the full list of $Q$ answers, which determines every prefix.
--
--   Differences from the source:
--   - generalization: probability at least 1 − 2(Q+1)e^{−δ²k/2} over A and the algorithm's randomness → for every fixed tape (deterministic rule P), the count of good k-sets A is at least that fraction of C(n, k); reason: the joint probability is the seed average of the per-tape fractions, so the per-tape bound implies it; needs no measurability
--   - encoding: an algorithm terminating almost surely and making at most Q current value queries before the last arrival on every model instance with n+1 elements → a rule with exactly Q query slots; reason: early stopping is padded with dummy queries; finiteness builds in termination
--   - encoding: a reference-oracle execution against ψ → the run of P against the restricted oracle of f_ref, whose answer on S ⊆ X is ψ(|S|/k); reason: same answers
--   - encoding: probability over a uniformly random k-subset A of X → number of k-subsets A of Fin n with the property, compared with the bound times C(n, k); reason: the uniform probability of an event is its count divided by C(n, k)
--   - encoding: X = [n] and the ground set X ∪ {r} → Fin n, embedded in Fin (n+1) by Fin.castSucc, with r = Fin.last n; reason: 0-based indices; same instances
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Lemma 5.3, p.16

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_QueryAlgorithm
import Definitions.Def_SharpConsist_fA
import Definitions.Def_SharpConsist_fref
import Definitions.Def_SharpConsist_uA

namespace SharpConsist

/-- **Lemma 5.3 (transcript hiding), for one random tape.** Fu–Zhang–Tao, *A Sharp Barrier of
Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2,
Lemma 5.3, p.16. Fix `T ∈ [7/5, 3/2]`, integers `m ≥ 32`, `k ≥ 1`, `n = (m+1)k`, `δ = 1/(64m)`, and
an adaptive rule `P` that makes `Q` value queries on subsets of `X` and then outputs a subset of `X`
(the pre-arrival phase of an algorithm with its random tape fixed). Among the `k`-subsets `A` of `X`,
at least a `1 − 2(Q+1)e^{−δ²k/2}` fraction satisfy: the answers `P` receives from `f_A` equal those it
receives from the reference oracle `f_ref` (Eq. (5.10)), its output against `f_A` equals its output
against `f_ref`, and that output has imbalance `|u_A| ≤ δ`.

**Formalization Note.** The paper's probability over `A` and the algorithm's randomness is the
average over tapes of this per-tape fraction, so the per-tape count implies it. The rule has exactly
`Q` query slots (`NonmonotoneSubmod.QueryLB.DetAlg`); answers are compared as the full list of `Q`
answers, which contains every prefix. -/
theorem lemma_5_3 (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m k n Q : ℕ) (hm : 32 ≤ m)
    (hk : 1 ≤ k) (hn : n = (m + 1) * k) (P : NonmonotoneSubmod.QueryLB.DetAlg (Fin n) Q) :
    (1 - 2 * ((Q : ℝ) + 1) * Real.exp (-(deltaM m ^ 2 * (k : ℝ) / 2))) * (n.choose k : ℝ) ≤
      (((Finset.univ.powersetCard k).filter (fun A : Finset (Fin n) =>
          P.answers (restrictX (fA T m k A)) Q = P.answers (restrictX (fref T m k (n := n))) Q ∧
          P.run (restrictX (fA T m k A)) = P.run (restrictX (fref T m k (n := n))) ∧
          |uA k m A (P.run (restrictX (fref T m k (n := n))))| ≤ deltaM m)).card : ℝ) := by sorry

end SharpConsist
