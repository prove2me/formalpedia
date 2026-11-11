-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_5
-- name    : SingleExpBisect.Main.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:42:10.216761+00:00
-- url     : https://prove2.me/theorems/8df95d5c-e637-4d9e-a510-19a8b2432830
-- title:
--   Lemma 3.5 — Z_t^{≤2k}(ω^{∂G_t}(y,x), w) at a large bag in O*(2^{O(k)}) time (G connected)
-- statement:
--   There are a constant $C$ and one deterministic machine such that, for every graph $G$ on $n$ vertices, $k\ge0$, decomposition $T$ as supplied by Theorem 1.1 and node $t$ with $|B_t|>4k+1$, given $(G,k,T,t)$ and the polynomials $Z_s(\omega_s^{\partial G_s}(y,x),w)$ of the children $s$ of $t$, it outputs the polynomial $Z_t^{\le2k}(\omega_t^{\partial G_t}(y,x),w)$ (its nonzero coefficients) within $C\cdot2^{Ck}(n+1)^C$ steps.
--
--   Differences from the source:
--   - reading: T is the decomposition supplied by Theorem 1.1 → IsSec3Decomp G T k: rooted tree decomposition, adhesion at most 2k, bags (2k,k)-edge-unbreakable in G, at most max n 1 nodes, and nonempty bags when n > 0; reason: the setup on p. 15 uses the construction; pp. 23 and 35 bound its number of bags by n and p. 35 puts a vertex in each bag; at n = 0 use one empty bag; the size bound prevents an unbounded decomposition input at fixed n
--   - encoding: running time O*(·) on an unspecified machine → one deterministic TM2 machine (published OutputsWithin) and one constant C, both chosen before the instance, with the stated step bound in n = |V| and the parameter; reason: the paper names no machine model; O* suppresses factors polynomial in the input size, whose length is polynomial in n up to a log-of-parameter term absorbed by the exponential factor
--   - encoding: "given Z_s(ω_s^{∂G_s}(y, x), w) for every child s" → the input lists, for each child s in increasing order, a sparse term list Lc s with IsSparseRep (distinct monomials, nonzero coefficients); the guarantee is required only when every Lc s represents Z_s(ω^{∂G_s}_s); reason: the paper fixes no input format; a canonical sparse list has length the number of monomials, as the paper counts
--   - reading: Lemma 3.5's sentence carries no bag-size hypothesis → |B_t| > 4k + 1; reason: Section 3.3 is the large-bag case fixed on p. 18 ("We now assume that |B_t| > 4k + 1")
--   - encoding: the polynomial is computed → the output is its sparse term list (IsSparseRep); reason: the paper's representation by coefficients
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.3, p. 22, Lemma 3.5

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.3, p. 22, Lemma 3.5: for a
graph `G`, a decomposition `T` as supplied by Theorem 1.1 and a node `t` with a large bag
(`|B_t| > 4k + 1`, the setting of §3.3), one machine, given `G, k, T, t` and the children's
polynomials `Z_s(ω_s^{∂G_s}(y, x), w)` (as sparse term lists), outputs the polynomial
`Z_t^{≤2k}(ω_t^{∂G_t}(y, x), w)` within `C · 2^{C·k} · (n + 1)^C` steps. -/
theorem lemma_3_5 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n) (t : Fin T.N)
        (Lc : Fin T.N → List ((Var n →₀ ℕ) × ℚ)),
        IsSec3Decomp G T k → 4 * k + 1 < (T.bag t).card →
        (∀ s, T.parent s = some t →
          IsSparseRep (Lc s) (fun e => MvPolynomial.coeff e (Zomega G T k s))) →
        ∃ L : List ((Var n →₀ ℕ) × ℚ),
          HMBinPacking.OutputsWithin M (nodeInput G k T t ++ childInput T t Lc)
            (encodeTerms L) (stepBound C k n) ∧
          IsSparseRep L (fun e => MvPolynomial.coeff e
            (omega (T.adhesion t) (Zle G (T.cone t) (T.bag t) k))) := by sorry

end SingleExpBisect.Main
