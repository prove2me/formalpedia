-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_4_2
-- name    : PPRInstOpt.UnknownN.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:14:27.443052+00:00
-- url     : https://prove2.me/theorems/8eba9f02-2da4-45a3-908b-ce019ccccb4c
-- title:
--   Lemma 4.2 — mean and variance of the Monte Carlo estimator
-- statement:
--   Let $(r_f,p_f,F_f,R_f)$ be the output of Algorithm 6 from $s$ with any budget $\kappa_f\ge 1$, $(r_b,p_b,F_b,\bar r_b)$ that of Algorithm 7 from $t$ with any budget $\kappa_b\ge1$, and $X$ the estimate returned by MonteCarloR$(q)$ (Algorithm 9) with these results, $q\ge1$, on a random tape. Then $X$ is integrable and
--   $$(1-\varepsilon_r/4)\,\pi(s,t)\le\mathbb E[X]\le\pi(s,t),\qquad \operatorname{Var}[X]\le\frac{R_f\,\bar r_b\,\pi(s,t)}{q}.$$
--   Together with Chebyshev's inequality this drives both the correctness and the stopping rule of TriPPR.
--
--   Differences from the source:
--   - encoding: E[Xγ], Var[Xγ] → Integrable X, Bochner integral ∫ X, and evariance X ≤ ENNReal.ofReal(R_f r̄_b π(s, t)/q); reason: evariance avoids the 0 junk value of a non-square-integrable variance; X is bounded, so nothing is lost
--   - reading: q(u) = q·rf(u)/Rf walks from u (§4.1) → q(u) = ⌈q rf(u)/Rf⌉ (Algorithm 9); reason: the algorithm's integer count
--   - reading: Rf, r̄b, rf, pf, Ff, rb, pb, Fb at the end of the push processes → outputs of Algorithm 6 and 7 runs with arbitrary budgets κf, κb ≥ 1; reason: Algorithm 8 passes results that may come from different rounds
--   - encoding: independent random walks; X1, X2, X3 independent; rounds independent → one tape of i.i.d. uniform [0, 1] entries (tapeLaw), read as independent streams; call γ of round i reads stream (i, γ); reason: the paper's randomness; independence by disjoint coordinates
--   - encoding: budget κ → natural number κ ≥ 1; reason: L_f and L_b divide by κ; Algorithm 8 only uses κ = 2^i
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 24, Lemma 4.2

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_TriPPR

open MeasureTheory ProbabilityTheory

namespace PPRInstOpt.UnknownN

/-- Lemma 4.2 (p. 24): let `F` be the output of Algorithm 6 from `s` with any budget `κ_f ≥ 1`,
`B` that of Algorithm 7 from `t` with any budget `κ_b ≥ 1`, and `X` the estimate of
`MonteCarloR(q)` (Algorithm 9, `q ≥ 1` walks in total) with these results on a random tape. Then
`X` is integrable, `(1 - εr/4) π(s, t) ≤ E[X] ≤ π(s, t)`, and `Var[X] ≤ R_f \bar r_b π(s, t)/q`. -/
theorem lemma_4_2 {V : Type} [Fintype V] [DecidableEq V] (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < εr) (hε1 : εr < 1) (G : Digraph V) (s t : V) (κf κb q : ℕ) (hκf : 1 ≤ κf)
    (hκb : 1 ≤ κb) (hq : 1 ≤ q) :
    Integrable (mcValue G.oracle α s q (fwdFinal G.oracle α εr κf s)
        (bwdFinal G.oracle α εr κb t)) tapeLaw ∧
    (1 - εr / 4) * ppr α G s t ≤
      ∫ ω, mcValue G.oracle α s q (fwdFinal G.oracle α εr κf s)
        (bwdFinal G.oracle α εr κb t) ω ∂tapeLaw ∧
    ∫ ω, mcValue G.oracle α s q (fwdFinal G.oracle α εr κf s)
        (bwdFinal G.oracle α εr κb t) ω ∂tapeLaw ≤ ppr α G s t ∧
    evariance (mcValue G.oracle α s q (fwdFinal G.oracle α εr κf s)
        (bwdFinal G.oracle α εr κb t)) tapeLaw ≤
      ENNReal.ofReal ((fwdFinal G.oracle α εr κf s).R * (bwdFinal G.oracle α εr κb t).R *
        ppr α G s t / q) := by sorry

end PPRInstOpt.UnknownN
