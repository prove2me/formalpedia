-- Prove2me | Theorems.Thm_SubexpPermanent_Main_theorem_7_1
-- name    : SubexpPermanent.Main.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:02:19.492196+00:00
-- url     : https://prove2.me/theorems/75dcf075-2f9b-497f-b535-ef1614bf684e
-- title:
--   Theorem 7.1 — deterministic counting: intervals of relative width $\xi$ for every $\mu_e$ and of width $\xi n$ for $\log Z(G)$ in time $\mathrm{poly}\cdot\exp(O(\sqrt\Lambda\log^2(\Lambda/\xi)))$
-- statement:
--   Let $n\ge1$ be an integer and $G$ a finite simple graph with at most $2n$ vertices and positive rational edge weights $w$ of total encoding length $S_G$, whose edge weights at each vertex sum to at most a rational $\Lambda\ge1$. There is one deterministic Turing machine and absolute constants $C$ and $d$ with the following property. For every rational $0<\xi<1/4$, the machine returns, for every edge $e$, a rational interval $[\ell_e,u_e]\ni\mu_e$ with $u_e-\ell_e\le\xi\mu_e$, and a rational interval $[\ell_Z,u_Z]\ni\log Z(G)$ with $u_Z-\ell_Z\le\xi n$, within
--   $$C\,(S_G+n+\operatorname{bits}\Lambda+\operatorname{bits}\xi)^d\exp\!\Big(C\sqrt\Lambda\log^2\frac\Lambda\xi\Big)$$
--   steps. Moreover, for every $\Delta$ there is $C_\Delta$ such that on graphs of maximum degree at most $\Delta$ the same run takes at most $C_\Delta(S_G+n+\operatorname{bits}\Lambda+\operatorname{bits}\xi)^d\exp(C_\Delta\sqrt\Lambda\log(\Lambda/\xi))$ steps. The exponential factor depends on the budget $\Lambda$ and not on the vertex degrees. This is the algorithmic contribution that makes the upper bound of Lemma 6.1 computable.
--
--   **Formalization Note.** The graph is given by its weight matrix $W$ (code `encMat W`), followed by `encRat Λ` and `encRat ξ`. The output lists the matrix of lower endpoints and the matrix of upper endpoints, each in the code `encMat`, then $\ell_Z$ and $u_Z$. For an edge $\{i,j\}$ the interval must be correct at both positions $(i,j)$ and $(j,i)$. Entries at non-edges are unconstrained.
--
--   Differences from the source:
--
--   - encoding: a deterministic algorithm counting bit operations on a Turing machine → one Mathlib Turing.FinTM2 machine with Boolean input and output alphabets (Turing.TM2ComputableAux Bool Bool) that halts with the output code on its output stack, all other stacks empty, within t steps (Turing.TM2OutputsInTime); reason: a TM2 step runs one statement of a fixed finite program; a Turing machine and a bit-operation algorithm simulate each other with polynomial overhead, which the time bounds absorb
--   - encoding: a finite simple graph with at most 2n vertices and positive rational edge weights of total encoding length S_G → a symmetric rational matrix W on Fin N (N ≤ 2n) with zero diagonal and nonnegative entries; the edges are its positive entries, with weight W_ij; the input code is encMat W, and S_G is read as its length; reason: every weighted graph on N vertices has such a matrix; |encMat W| is at least the weights' encoding length and at most a fixed polynomial in it and n, so the polynomial factor is unchanged up to the absolute constants
--   - reading: Let n ≥ 1 be an integer, and let G be a graph with at most 2n vertices (n a parameter of the statement) → the machine receives W, Λ and the accuracy only; its guarantee and time bound hold for every n ≥ 1 with N ≤ 2n; reason: n is not described as an input; a machine that does not read n is the stronger reading and specializes to one that is given n
--   - reading: running time poly(S_G + n + bits Λ + bits ξ)·exp(O(√Λ log²(Λ/ξ))) with absolute constants and an absolute polynomial degree → ∃ C : ℝ, ∃ d : ℕ fixed before every input with t ≤ C·(|encMat W| + n + |encRat Λ| + |encRat ξ|)^d·exp(C·√Λ·log²(Λ/ξ)); reason: an explicit absolute constant and degree for O(·) and poly; the base is at least 1, so C·base^d dominates every polynomial of degree d with bounded coefficients
--   - reading: if the maximum degree is a fixed Δ, the squared logarithm can be replaced by a single logarithm, with constants depending on Δ → for the same machine and the same absolute degree d: ∀ Δ, ∃ C_Δ, every input with maximum degree ≤ Δ runs in t ≤ C_Δ·base^d·exp(C_Δ·√Λ·log(Λ/·)); reason: the stronger, single-algorithm reading; the proof on p. 28 keeps the absolute polynomial degree, and one machine can run both recursions in parallel and stop at the first to finish
--   - encoding: for every edge e an interval with rational endpoints, and an interval for log Z(G) → output code encMat lo ++ encMat up ++ encRat ℓ_Z ++ encRat u_Z, with the interval of edge {i, j} at both positions (i, j) and (j, i) and arbitrary entries at non-edges; reason: a binary code listing every edge's endpoints; writing an edge's interval twice changes no time bound
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), p. 25, Theorem 7.1

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Encoding
import Definitions.Def_SubexpPermanent_Main_Matchings
import Definitions.Def_SubexpPermanent_Main_Machines
open ContinualHardness.Linear

namespace SubexpPermanent.Main

/-- Theorem 7.1, p. 25: one deterministic machine returns rational intervals for every edge
probability (width at most `ξ μ_e`) and for `log Z(G)` (width at most `ξ n`), with the general
running-time bound and, for each fixed maximum degree `Δ`, the single-logarithm bound. The graph
on `Fin N` (`N ≤ 2n`) is given by its symmetric weight matrix `W` (zero diagonal, nonnegative
entries; the edges are the positive entries). The output lists the matrices of lower and of upper
endpoints (entries at non-edges are unconstrained), then the interval for `log Z(G)`. -/
theorem theorem_7_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C : ℝ) (d : ℕ),
      ∀ Δ : ℕ, ∃ CΔ : ℝ,
        ∀ (n N : ℕ) (W : Matrix (Fin N) (Fin N) ℚ) (Λ ξ : ℚ),
          1 ≤ n → N ≤ 2 * n →
          (∀ i j, W i j = W j i) → (∀ i, W i i = 0) → (∀ i j, 0 ≤ W i j) →
          (∀ i, ∑ j, W i j ≤ Λ) → 1 ≤ Λ → 0 < ξ → ξ < 1 / 4 →
          ∃ (lo up : Matrix (Fin N) (Fin N) ℚ) (lz uz : ℚ) (t : ℕ),
            (∀ i j, (adjGraph W).Adj i j →
              (lo i j : ℝ) ≤ edgeProb (adjGraph W) (adjWeight W) Finset.univ s(i, j) ∧
              edgeProb (adjGraph W) (adjWeight W) Finset.univ s(i, j) ≤ up i j ∧
              ((up i j - lo i j : ℚ) : ℝ) ≤
                ξ * edgeProb (adjGraph W) (adjWeight W) Finset.univ s(i, j)) ∧
            (lz : ℝ) ≤ Real.log (matchingZ (adjGraph W) (adjWeight W) Finset.univ) ∧
            Real.log (matchingZ (adjGraph W) (adjWeight W) Finset.univ) ≤ uz ∧
            uz - lz ≤ ξ * n ∧
            OutputsWithin M (encMat W ++ encRat Λ ++ encRat ξ)
              (encMat lo ++ encMat up ++ encRat lz ++ encRat uz) t ∧
            (t : ℝ) ≤ C * (((encMat W).length + n + (encRat Λ).length + (encRat ξ).length : ℕ) : ℝ) ^ d *
              Real.exp (C * Real.sqrt Λ * Real.log ((Λ : ℝ) / ξ) ^ 2) ∧
            (MaxDegreeLE W Δ →
              (t : ℝ) ≤ CΔ * (((encMat W).length + n + (encRat Λ).length + (encRat ξ).length : ℕ) : ℝ) ^ d *
                Real.exp (CΔ * Real.sqrt Λ * Real.log ((Λ : ℝ) / ξ))) := by sorry

end SubexpPermanent.Main
