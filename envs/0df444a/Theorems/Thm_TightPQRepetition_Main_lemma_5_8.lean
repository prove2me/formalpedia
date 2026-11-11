-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_5_8
-- name    : TightPQRepetition.Main.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:44:09.374227+00:00
-- url     : https://prove2.me/theorems/6b3fc582-7a51-4a4e-bcc4-750e997c4c37
-- title:
--   Lemma 5.8 — ideal rejection-sampling success
-- statement:
--   Let $B$ be a prover with
--   $$\Pr[\langle B,\widehat V^{k',t'}\rangle(1^\lambda)=1]\ge B(k',t',\varepsilon)+\frac{10k'-1}{10k}\nu$$
--   satisfying the tail bounds of Theorem 5.1, with $1<k'\le k$, $t'\le k'$, $\nu>0$, and $2^{-\lambda}<\nu/10k$. Then
--   $$\Pr_{\tau\leftarrow H_m}[V(\tau_1,r_{{\rm Ver},1})=1]\ge\varepsilon+\frac{3\nu}{5k}.$$
--   The hybrid $H_m$ retries at most $N$ times and may abort, and the bound includes this failure.
--
--   Differences from the source:
--   - encoding: H_m with its output τ → hmAccept: the probability, by recursion on the attempts left, that a transcript is output and the first subverifier accepts; reason: a finite geometric sum, so no conditioning on a null event
--   - encoding: rounds and coordinates numbered from 1 → numbered from 0; the source's coordinate 1 is coordinate 0; reason: same instances
--   - encoding: efficiently computable ε(λ) ≥ 0 → ε(λ) ∈ [0,1], efficiently computable by a polynomial-time Turing machine to any requested precision; reason: [0,1] is the domain of B(k,t,ε) in Notation 2
--   - generalization: B is QPT → B is any valid strategy at the fixed λ, and the scheme any `EncScheme`; reason: the lemma is a statement about one law
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 5.8, printed p. 32 / PDF p. 34; proof Appendix A.2, printed pp. 36–38 / PDF pp. 38–40; standing assumption 2^{-λ} < ν/10k, printed p. 23 / PDF p. 25

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Reduction

namespace TightPQRepetition.Main

/-- Lemma 5.8 (printed p. 32, PDF p. 34; proof PDF pp. 38–40). -/
theorem lemma_5_8 (x : RedCtx) (hE : x.E.IsEfficient) (hV : x.V.IsEfficient) (hB : x.B.Valid)
    (hk' : 1 < x.k') (hk : x.k' ≤ x.k) (ht : x.t' ≤ x.k') (hν : 0 < x.ν)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hlam : (1 / 2 : ℝ) ^ x.lam < x.ν / (10 * x.k))
    (hacc : binomTail x.k' x.t' ε + (10 * (x.k' : ℝ) - 1) / (10 * x.k) * x.ν ≤
      x.B.acceptProb x.par x.lam)
    (htail : TailBounds x.E x.V x.B x.lam x.k x.k' x.t' x.ν ε) :
    ε + 3 * x.ν / (5 * x.k) ≤ x.hmAccept := by sorry

end TightPQRepetition.Main
