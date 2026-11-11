-- Prove2me | Theorems.Thm_SubexpPermanent_Main_lemma_7_2
-- name    : SubexpPermanent.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:01:57.513607+00:00
-- url     : https://prove2.me/theorems/1514da94-08cf-41d0-9db0-65510602ce87
-- title:
--   Lemma 7.2 — deterministic estimates $z\in I^{V}$ of the unmatched probabilities with $|\log z_v-\log q_G(v)|\le\delta/4$ in time $\mathrm{poly}\cdot\exp(O(\sqrt\Lambda\log^2(\Lambda/\delta)))$
-- statement:
--   Let $n\ge1$ and let $G$ be a finite simple graph with at most $2n$ vertices and positive rational edge weights $w$ of total encoding length $S_G$. Suppose the edge weights at each vertex sum to at most a rational $\Lambda\ge1$. Let $\gamma=\lceil\Lambda\rceil$, $c=1+\gamma$, $I=[1/c,1]$, and let $q_G(v)$ be the probability that $v$ is unmatched under $\nu_{G,w}$. There is one deterministic Turing machine and absolute constants $C$ and $d$ with the following property. For every rational $0<\delta<1/4$, the machine computes a rational vector $z\in I^{V(G)}$ with
--   $$|\log z_v-\log q_G(v)|\le\delta/4\qquad(v\in V(G)),$$
--   within
--   $$C\,(S_G+n+\operatorname{bits}\Lambda+\operatorname{bits}\delta)^d\exp\!\Big(C\sqrt\Lambda\log^2\frac\Lambda\delta\Big)$$
--   steps. Moreover, for every $\Delta$ there is $C_\Delta$ such that on graphs of maximum degree at most $\Delta$ the same run takes at most $C_\Delta(S_G+n+\operatorname{bits}\Lambda+\operatorname{bits}\delta)^d\exp(C_\Delta\sqrt\Lambda\log(\Lambda/\delta))$ steps. It is the key step of the counting algorithm of Theorem 7.1.
--
--   **Formalization Note.** The graph is given by its weight matrix $W$ in the code `encMat`, followed by `encRat Λ` and `encRat δ`; the output is `encList encRat` of $(z_0,\dots,z_{N-1})$. $S_G$, $\operatorname{bits}\Lambda$ and $\operatorname{bits}\delta$ are the lengths of these codes.
--
--   Differences from the source:
--
--   - encoding: a deterministic algorithm counting bit operations on a Turing machine → one Mathlib Turing.FinTM2 machine with Boolean input and output alphabets (Turing.TM2ComputableAux Bool Bool) that halts with the output code on its output stack, all other stacks empty, within t steps (Turing.TM2OutputsInTime); reason: a TM2 step runs one statement of a fixed finite program; a Turing machine and a bit-operation algorithm simulate each other with polynomial overhead, which the time bounds absorb
--   - encoding: a finite simple graph with at most 2n vertices and positive rational edge weights of total encoding length S_G → a symmetric rational matrix W on Fin N (N ≤ 2n) with zero diagonal and nonnegative entries; the edges are its positive entries, with weight W_ij; the input code is encMat W, and S_G is read as its length; reason: every weighted graph on N vertices has such a matrix; |encMat W| is at least the weights' encoding length and at most a fixed polynomial in it and n, so the polynomial factor is unchanged up to the absolute constants
--   - reading: Let n ≥ 1 be an integer, and let G be a graph with at most 2n vertices (n a parameter of the statement) → the machine receives W, Λ and the accuracy only; its guarantee and time bound hold for every n ≥ 1 with N ≤ 2n; reason: n is not described as an input; a machine that does not read n is the stronger reading and specializes to one that is given n
--   - reading: running time poly(S_G + n + bits Λ + bits δ)·exp(O(√Λ log²(Λ/δ))) with absolute constants and an absolute polynomial degree → ∃ C : ℝ, ∃ d : ℕ fixed before every input with t ≤ C·(|encMat W| + n + |encRat Λ| + |encRat δ|)^d·exp(C·√Λ·log²(Λ/δ)); reason: an explicit absolute constant and degree for O(·) and poly; the base is at least 1, so C·base^d dominates every polynomial of degree d with bounded coefficients
--   - reading: if the maximum degree is a fixed Δ, the squared logarithm can be replaced by a single logarithm, with constants depending on Δ → for the same machine and the same absolute degree d: ∀ Δ, ∃ C_Δ, every input with maximum degree ≤ Δ runs in t ≤ C_Δ·base^d·exp(C_Δ·√Λ·log(Λ/·)); reason: the stronger, single-algorithm reading; the proof on p. 28 keeps the absolute polynomial degree, and one machine can run both recursions in parallel and stop at the first to finish
--   - encoding: I = [1/c, 1] with c = 1 + γ, γ = ⌈Λ⌉ → unmatchedInterval ⌈Λ⌉ = [1/(1 + ⌈Λ⌉), 1]; reason: the same interval
--   - encoding: a rational vector z ∈ I^{V(G)} returned → the output code encList encRat (z_0, …, z_{N−1}); reason: binary code of the returned vector in vertex order
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 25, Lemma 7.2

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Encoding
import Definitions.Def_SubexpPermanent_Main_Matchings
import Definitions.Def_SubexpPermanent_Main_Contraction
import Definitions.Def_SubexpPermanent_Main_Machines
open ContinualHardness.Linear

namespace SubexpPermanent.Main

/-- Lemma 7.2, p. 25: one deterministic machine estimates every unmatched probability within
`δ/4` in log scale, with the general running-time bound and, for each fixed maximum degree `Δ`,
the single-logarithm bound. The graph on `Fin N` (`N ≤ 2n`) is given by its symmetric weight
matrix `W` (zero diagonal, nonnegative entries; the edges are the positive entries). -/
theorem lemma_7_2 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℝ) (d : ℕ),
      ∀ Δ : ℕ, ∃ CΔ : ℝ,
        ∀ (n N : ℕ) (W : Matrix (Fin N) (Fin N) ℚ) (Λ δ : ℚ),
          1 ≤ n → N ≤ 2 * n →
          (∀ i j, W i j = W j i) → (∀ i, W i i = 0) → (∀ i j, 0 ≤ W i j) →
          (∀ i, ∑ j, W i j ≤ Λ) → 1 ≤ Λ → 0 < δ → δ < 1 / 4 →
          ∃ (z : Fin N → ℚ) (t : ℕ),
            (∀ v, (z v : ℝ) ∈ unmatchedInterval (⌈(Λ : ℝ)⌉ : ℝ)) ∧
            (∀ v, |Real.log (z v) -
                Real.log (unmatchedProb (adjGraph W) (adjWeight W) Finset.univ v)| ≤ (δ : ℝ) / 4) ∧
            OutputsWithin M (encMat W ++ encRat Λ ++ encRat δ) (encList encRat (List.ofFn z)) t ∧
            (t : ℝ) ≤ C * (((encMat W).length + n + (encRat Λ).length + (encRat δ).length : ℕ) : ℝ) ^ d *
              Real.exp (C * Real.sqrt Λ * Real.log ((Λ : ℝ) / δ) ^ 2) ∧
            (MaxDegreeLE W Δ →
              (t : ℝ) ≤ CΔ * (((encMat W).length + n + (encRat Λ).length + (encRat δ).length : ℕ) : ℝ) ^ d *
                Real.exp (CΔ * Real.sqrt Λ * Real.log ((Λ : ℝ) / δ))) := by sorry

end SubexpPermanent.Main
