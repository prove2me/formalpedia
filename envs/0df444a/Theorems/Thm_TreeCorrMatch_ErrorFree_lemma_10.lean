-- Prove2me | Theorems.Thm_TreeCorrMatch_ErrorFree_lemma_10
-- name    : TreeCorrMatch.ErrorFree.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:26:14.880187+00:00
-- url     : https://prove2.me/theorems/e9680c41-2f70-4037-8b9e-bd0919664e95
-- title:
--   Lemma 10 — if every $\hat S_q$ is within $1\pm\delta$ of $S_q(\hat Z)$, then $e^{-1/16}L_d\le\hat L_d\le e^{1/16}L_d$
-- statement:
--   Let $\lambda>0$, $s\in(0,1]$, $\xi\in(0,\tfrac12)$ and $d\ge0$, and fix trees $t,\tilde t$ of depth at most $d$. Run ApproxLR on $(t,\tilde t)$ with parameters $\lambda,s,\xi,d$, and let $\delta$ be the accuracy fixed in Step 1. Suppose that for every $h\in[1:d]$, every pair of vertices $(u,\tilde v)$ at depth $d-h$ of $t$ and $\tilde t$, and every $q\in[1:\min\{c,\tilde c\}]$, the value $\hat S_q(u,\tilde v)$ computed in (18) satisfies
--
--   $$(1-\delta)\,S_q(\hat Z(u,\tilde v))\le\hat S_q(u,\tilde v)\le(1+\delta)\,S_q(\hat Z(u,\tilde v)).$$
--
--   Then
--
--   $$e^{-1/16}L_d(t,\tilde t)\le\hat L_d(t,\tilde t)\le e^{1/16}L_d(t,\tilde t).$$
--
--   The statement is deterministic: it holds for whatever values the permanent approximator returned. It shows that the choice $\delta=1/(64D^d)$ keeps the accumulated relative error within a factor $e^{\pm1/16}$.
--
--   **Formalization Note** The approximator `App` and the seeds `ω` are arbitrary; vertices at depth $d-h$ are positions of length $d-h$, and $\hat Z$, $\hat S_q$ are the algorithm's own intermediate values `zhat`, `shat`.
--
--   Differences from the source:
--   - encoding: (t, t̃) ∈ Z_d × Z_d with children enumerated in an unspecified order → ordered trees of depth ≤ d, children in list order; reason: the statement holds for every ordered representative, hence for every enumeration
--   - encoding: the values Ŝ_q produced by ApproxPer during one run → an arbitrary function App and arbitrary seeds ω, with the hypothesis on the resulting values; reason: the lemma is deterministic in the computed values
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), p. 34, Lemma 10 (PDF p. 36)

import Mathlib
import Definitions.Def_TreeCorrMatch_ErrorFree_TreePairLaws
import Definitions.Def_TreeCorrMatch_ErrorFree_ApproxLR

namespace TreeCorrMatch.ErrorFree

theorem lemma_10 {Ω₀ : Type} (App : PermApprox Ω₀) (lam s ξ : ℝ) (d : ℕ) (hlam : 0 < lam)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2) (t t' : OTree)
    (ht : t.depth ≤ d) (ht' : t'.depth ≤ d) (ω : SeedIdx → Ω₀)
    (hacc : ∀ h ∈ Finset.Icc 1 d, ∀ (p p' : List ℕ) (u u' : OTree),
      p.length = d - h → p'.length = d - h → t.subtreeAt p = some u → t'.subtreeAt p' = some u' →
      ∀ q ∈ Finset.Icc 1 (min u.children.length u'.children.length),
        (1 - alrDelta d t t') *
            matchingSum
              (zhat lam s (lhat App lam s (alrDelta d t t') (alrEta ξ d t t') ω (h - 1)) p p' u u')
              q ≤
          shat App (alrDelta d t t') (alrEta ξ d t t') ω p p'
            (zhat lam s (lhat App lam s (alrDelta d t t') (alrEta ξ d t t') ω (h - 1)) p p' u u')
            q ∧
        shat App (alrDelta d t t') (alrEta ξ d t t') ω p p'
            (zhat lam s (lhat App lam s (alrDelta d t t') (alrEta ξ d t t') ω (h - 1)) p p' u u')
            q ≤
          (1 + alrDelta d t t') *
            matchingSum
              (zhat lam s (lhat App lam s (alrDelta d t t') (alrEta ξ d t t') ω (h - 1)) p p' u u')
              q) :
    Real.exp (-(1 / 16)) * likelihoodRatio lam s d (cls t) (cls t') ≤
        approxLR App lam s ξ d t t' ω ∧
      approxLR App lam s ξ d t t' ω ≤ Real.exp (1 / 16) * likelihoodRatio lam s d (cls t) (cls t') := by sorry

end TreeCorrMatch.ErrorFree
