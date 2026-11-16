-- Prove2me | Theorems.Thm_SubmodMDP_Policies_Supplement_lemma_14
-- name    : SubmodMDP.Policies.Supplement.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:24.637101+00:00
-- url     : https://prove2.me/theorems/5f94d624-2c95-4f56-8f89-2b8594629dc1
-- title:
--   Lemma 14 — Algorithm 5 returns a path with its exact factor and runtime
-- statement:
--   Let $G=(V,A)$ be a well-formed layered graph with layers $V_1,\ldots,V_H$, where $H=d^r$, $d\ge2$ and $r\ge0$ are integers. Let $S\subseteq V_1$ and $T\subseteq V_H$, assume an $S$-$T$ path exists, and let $f$ be a nonnegative monotone submodular value oracle.
--
--   There are one positive absolute integer $c$ and one deterministic program, uniform over all these data and oracles, implementing Algorithm 5 in at most $(|V|+1)^{c(r+1)}$ charged operations. Its result is a path $P\ne\bot$ from $S$ to $T$, and for every $S$-$T$ path $Q$,
--
--   $$f(P)\ge\frac{f(Q)}{(d-1)(r+1)}.$$
--
--   In particular the inequality holds for a reward-maximizing path. Algorithm 5 is defined by the recursive dynamic program, including the full stored-prefix marginal and the singleton base case. This lemma supports Theorem 15; neither its exact ratio nor its runtime is replaced by an assumed field.
--
--   Differences from the source:
--   - reading: word-RAM operations with input and oracle values fitting a word (footnote 2) → the unchanged published word-charged integer RAM, including its value query and uniform rand M; reason: reuse the accepted base machine model; word length covers input integers and all oracle numerators and denominators, and every RAM run must halt within the bound
--   - reading: nonnegative real-valued oracle rewards → nonnegative rational-valued oracle rewards, using the accepted base finite-representation convention; reason: footnote 2 requires finite word representations; no normalization, integral-reward hypothesis or magnitude bound is added
--   - encoding: n^{O(r)} runtime and factor 1/((d−1)(r+1)) against an optimal path → one positive absolute integer c and one deterministic RAM program, cost at most (n+1)^{c(r+1)}, with the same exact factor against every feasible path; reason: the maximum exists among finitely many layer-spanning paths, so universal comparison is equivalent; n+1 and r+1 cover n=1 and r=0
--   - encoding: induced consecutive-layer blocks, ⊥ and unspecified ties in Algorithm 5 → an offset into the published LGraph, Option paths, strict-improvement updates and increasing-index tie order; reason: the offset restricts every recursive singleton to its own block; each chosen tie is a permitted maximizer; no restriction to singleton endpoints or positive r is made
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 14 and Algorithm 5, p. 24 (PDF p. 25); proof, p. 25 (PDF p. 26)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Supplement_Algorithm5

namespace SubmodMDP.Policies.Supplement

/-- Lemma 14, printed p. 24 (PDF p. 25), including the runtime conclusion.
The same deterministic RAM program implements Algorithm 5 for every d,r and every oracle.
The approximation is stated against every feasible path, equivalently against the maximum. -/
theorem lemma_14 :
    ∃ c : ℕ, 0 < c ∧ ∃ Alg : Program, Alg.Deterministic ∧
    ∀ (G : LGraph), G.WF → ∀ d r : ℕ, 2 ≤ d → G.H = d ^ r →
    ∀ S T : Finset (Fin G.N),
      (∀ v ∈ S, G.layer v = 1) → (∀ v ∈ T, G.layer v = G.H) →
      (∃ P, STPath G S T P) →
    ∀ f : Finset (Fin G.N) → ℚ, Reward f →
    let O : Oracle := ⟨G.N, f⟩
    let inp := encDP G d r S T
    let B := (G.N + 1) ^ (c * (r + 1))
    Computes Alg O (wordLen inp O) inp B (encOptionalWalk (alg5 G d r 0 S T f)) ∧
    ∃ P, alg5 G d r 0 S T f = some P ∧ STPath G S T P ∧
      ∀ Q, STPath G S T Q →
        (f Q.toFinset : ℝ) / (((d : ℝ) - 1) * ((r : ℝ) + 1)) ≤ (f P.toFinset : ℝ) := by sorry

end SubmodMDP.Policies.Supplement
