-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_4
-- name    : SingleExpBisect.Main.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:41:59.005755+00:00
-- url     : https://prove2.me/theorems/b5df09b4-bf1b-4a01-a685-bf07c1176a93
-- title:
--   Lemma 3.4 — all coefficients of ⟨L_{t,S}(ω^{B_t}(y,x), w)⟩_{≤(k,n,2k)} in O*(2^{O(k)}) time
-- statement:
--   There are a constant $C$ and one deterministic machine such that, for every graph $G$ on $n$ vertices, $k\ge0$, decomposition $T$ as supplied by Theorem 1.1, node $t$ and $S\subseteq B_t$ with $|S|\le2k$, given $(G,k,T,t,S)$ and the polynomials $Z_s(\omega_s^{\partial G_s}(y,x),w)$ of the children $s$ of $t$, it outputs all nonzero coefficients of $\langle L_{t,S}(\omega_t^{B_t}(y,x),w)\rangle_{\le(k,n,2k)}$ within $C\cdot2^{Ck}(n+1)^C$ steps.
--
--   Differences from the source:
--   - reading: T is the decomposition supplied by Theorem 1.1 → IsSec3Decomp G T k: rooted tree decomposition, adhesion at most 2k, bags (2k,k)-edge-unbreakable in G, at most max n 1 nodes, and nonempty bags when n > 0; reason: the setup on p. 15 uses the construction; pp. 23 and 35 bound its number of bags by n and p. 35 puts a vertex in each bag; at n = 0 use one empty bag; the size bound prevents an unbounded decomposition input at fixed n
--   - encoding: running time O*(·) on an unspecified machine → one deterministic TM2 machine (published OutputsWithin) and one constant C, both chosen before the instance, with the stated step bound in n = |V| and the parameter; reason: the paper names no machine model; O* suppresses factors polynomial in the input size, whose length is polynomial in n up to a log-of-parameter term absorbed by the exponential factor
--   - encoding: "given Z_s(ω_s^{∂G_s}(y, x), w) for every child s" → the input lists, for each child s in increasing order, a sparse term list Lc s with IsSparseRep (distinct monomials, nonzero coefficients); the guarantee is required only when every Lc s represents Z_s(ω^{∂G_s}_s); reason: the paper fixes no input format; a canonical sparse list has length the number of monomials, as the paper counts
--   - generalization: S ∈ C_t (Lemma 3.3) → any S ⊆ B_t with |S| ≤ 2k; reason: every member of C_t is such a set and the proof uses only |S| ≤ 2k
--   - generalization: the setting of Section 3.3: |B_t| > 4k+1 → no bag-size hypothesis; reason: the computation on pp. 20–21 uses only |S| ≤ 2k; the large-bag case is included
--   - encoding: "all coefficients" of the truncated series → IsSparseRep of the output: exactly the nonzero coefficients, each once; reason: the omitted coefficients are zero
--   - encoding: L_{t,S}(ω_t^{B_t}(y, x), w) → renamePS (omegaVar B_t) (LtS G (cone t) (bag t) k S); reason: the substitution applied to the series L_{t,S}(y, w) as printed
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.3, p. 20, Lemma 3.4

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.3, p. 20, Lemma 3.4: for a
decomposition `T` as supplied by Theorem 1.1, a node `t` and `S ⊆ B_t` with `|S| ≤ 2k` (every
member of `C_t`), one machine, given `G, k, T, t, S` and the children's polynomials
`Z_s(ω_s^{∂G_s}(y, x), w)` (as sparse term lists), outputs all nonzero coefficients of
`⟨L_{t,S}(ω_t^{B_t}(y, x), w)⟩_{≤(k,n,2k)}` within `C · 2^{C·k} · (n + 1)^C` steps. -/
theorem lemma_3_4 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n) (t : Fin T.N)
        (S : Finset (Fin n)) (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ)),
        IsSec3Decomp G T k → S ⊆ T.bag t → S.card ≤ 2 * k →
        (∀ s, T.parent s = some t →
          IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) →
        ∃ L : List ((Var n →₀ ℕ) × ℚ),
          HMBinPacking.OutputsWithin M (nodeInput G k T t ++ encodeSet S ++ childInput T t Lc)
            (encodeTerms L) (stepBound C k n) ∧
          IsSparseRep L (fun e => MvPowerSeries.coeff e
            (truncKNB k n (T.bag t)
              (renamePS (omegaVar (T.bag t)) (LtS G (T.cone t) (T.bag t) k S)))) := by sorry

end SingleExpBisect.Main
