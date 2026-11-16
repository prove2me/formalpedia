-- Prove2me | Theorems.Thm_SubmodMDP_Policies_Supplement_theorem_1
-- name    : SubmodMDP.Policies.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:42.331409+00:00
-- url     : https://prove2.me/theorems/763961c1-59c3-468a-b226-ff280e468b3b
-- title:
--   Theorem 1 — LP-based orienteering in both approximation regimes
-- statement:
--   Let $G=(V,A)$ be a finite directed graph with $n=|V|$, endpoints $s,t$, nonnegative integral arc lengths $w$, and budget $C\ge0$. Let $f$ be a nonnegative monotone submodular value oracle on vertex sets. Assume that a budget-feasible $s$-$t$ walk exists, and let $\mathrm{OPT}$ be its maximum reward. There are positive absolute constants $K,c,c_{\rm Pre}$, a fixed LP preprocessing program, a logarithmic-regime program, and an integer-indexed family of polynomial-regime programs with both following guarantees.
--
--   The logarithmic-regime program outputs an $s$-$t$ walk on every run, in at most $\lceil(n+1)^{c(\log_2 n+1)}\rceil(\langle w\rangle+1)^c$ charged operations, and
--
--   $$\mathbb E[f(W)]\ge\frac{\mathrm{OPT}}{K(\log_2 n+1)},\qquad \mathbb E[w(W)]\le C.$$
--
--   For every real $\varepsilon>0$ there is $K_\varepsilon>0$, independent of the instance and oracle, such that the polynomial-regime program with integer parameter $k=\max\{1,\lceil2/\varepsilon\rceil\}$ outputs an $s$-$t$ walk on every run, in at most $(n+1)^{ck}(\langle w\rangle+1)^c$ charged operations, and
--
--   $$\mathbb E[f(W)]\ge\frac{\mathrm{OPT}}{K_\varepsilon n^\varepsilon},\qquad \mathbb E[w(W)]\le C.$$
--
--   Both programs implement the published constrained LP interface at fixed accuracy $\delta=1/2$, followed by an independent RRR sample and reconstruction. Their full expectation additionally satisfies the proof's exact bound
--
--   $$\mathbb E[f(W)]\ge\frac{(1-N^{-2})/2}{(d-1)(r+1)}\,\mathrm{OPT},$$
--
--   where $N$ is the number of reduced vertices and $d,r$ are the specified reduction parameters. Every preprocessing outcome is LP-feasible; the expectation includes unsuccessful reward-preprocessing runs. The cost includes graph construction, shortest paths, oracle simulation, preprocessing, sampling and reconstruction. This companion result supplies the paper's LP-based directed-walk approximation, separately from its MDP policy goal.
--
--   Differences from the source:
--   - reading: word-RAM operations with input and oracle values fitting a word (footnote 2) → the unchanged published word-charged integer RAM, including its value query and uniform rand M; reason: reuse the accepted base machine model; word length covers input integers and all oracle numerators and denominators, and every RAM run must halt within the bound
--   - reading: nonnegative real-valued oracle rewards → nonnegative rational-valued oracle rewards, using the accepted base finite-representation convention; reason: footnote 2 requires finite word representations; no normalization, integral-reward hypothesis or magnitude bound is added
--   - encoding: arbitrary finite directed s-t walks and their optimum → Mathlib Digraph on Fin n and the maximum over achievable visited sets; reason: walks may repeat vertices and arcs, s=t and zero-length walks are retained; the visited-set family is finite and feasible inputs attain its maximum
--   - encoding: arbitrary nonnegative real budget C → the effective integer budget floor C, then internally clipped to Hn max_a w(a); reason: integer walk lengths make feasibility and the expected-budget conclusion equivalent to or stronger than the real-budget statement; zero budget and zero arc lengths remain allowed
--   - encoding: logarithmic regime O(log n), n^{O(log n)}⟨w⟩^{O(1)}, and the proof transfer factor → absolute K,c,cPre before all instances; ratio K(log₂ n+1), cost ceil((n+1)^{c(log₂ n+1)})(⟨w⟩+1)^c, and the exact proof factor with δ=1/2; reason: the shifts include n=1; fixing δ independently of ε gives (1−N^{-2})/2 and hence at least 3/8 for N≥2; the preprocessing contract and equality of full output laws give the LP-based clause formal content
--   - encoding: O(n^ε) ratio and n^{O(1/ε)} runtime for every ε>0 → K_ε after ε, one absolute exponent c before ε, integer parameter k=max(1,ceil(2/ε)) and cost (n+1)^{ck}; reason: integer and large-ε runtime convention; it is O(1/ε) for 0<ε≤1 and a fixed polynomial for ε≥1; the program family is chosen before ε and never receives a real number
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Theorem 1, p. 1 (PDF p. 2); proof, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Supplement_Pipeline

namespace SubmodMDP.Policies.Supplement

/-- Theorem 1, printed p. 1 (PDF p. 2), proof printed p. 14 (PDF p. 15).
Both regimes use the same constrained LP preprocessing contract at δ=1/2, followed by an
independent RRR sample and reconstruction. c and the logarithmic ratio constant are absolute;
only the polynomial ratio constant depends on ε. -/
theorem theorem_1 :
    ∃ c cPre : ℕ, 0 < c ∧ 0 < cPre ∧ ∃ K : ℝ, 0 < K ∧
    ∃ Pre AlgLog : Program, ∃ AlgPoly : ℕ → Program,
    (∀ (n : ℕ) (I : Ori n) (w : Fin n → Fin n → ℕ) (C : ℕ),
      (∃ W, Walk I.graph I.s I.t W ∧ walkLength w W ≤ C) →
      ∀ f : Finset (Fin n) → ℚ, Reward f →
        LPGuarantee AlgLog Pre cPre I 2 (logDepth n) w C
          (logTime n c * (sizeW I w + 1) ^ c) f (K * (Real.logb 2 n + 1))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Kε : ℝ, 0 < Kε ∧
      ∀ (n : ℕ) (I : Ori n) (w : Fin n → Fin n → ℕ) (C : ℕ),
        (∃ W, Walk I.graph I.s I.t W ∧ walkLength w W ≤ C) →
        ∀ f : Finset (Fin n) → ℚ, Reward f →
          LPGuarantee (AlgPoly (epsK ε)) Pre cPre I (polyDegree n (epsK ε))
            (polyDepth n (epsK ε)) w C
            (polyTime n (epsK ε) c * (sizeW I w + 1) ^ c) f (Kε * (n : ℝ) ^ ε)) := by sorry

end SubmodMDP.Policies.Supplement
