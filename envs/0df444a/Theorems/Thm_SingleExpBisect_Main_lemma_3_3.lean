-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_3
-- name    : SingleExpBisect.Main.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:42:11.199349+00:00
-- url     : https://prove2.me/theorems/2482c630-1a7a-4b92-8722-26f01875c60a
-- title:
--   Lemma 3.3 — the B_t-supports of log Z_t^{≤2k}(ω^{B_t}(y,x), w) lie in an enumerable family C_t (G connected)
-- statement:
--   There are a constant $C$ and one deterministic machine such that, for every graph $G$ on $n$ vertices, $k\ge0$, decomposition $T$ as supplied by Theorem 1.1 and node $t$, it outputs on input $(G,k,T,t)$ within $C\cdot2^{Ck}(n+1)^C$ steps a list of a downward-closed family $\mathcal C_t\subseteq2^{B_t}$ with $|\mathcal C_t|\le C\cdot2^{Ck}(n+1)^C$, every member of size at most $2k$, such that for all $b,\ell\ge0$ and $(a_v)_{v\in B_t}$ with $\ell\le k$ and $|\{v\in B_t:a_v>0\}|\le2k$:
--   $$\Big[x^bw^\ell\prod_{v\in B_t}y_v^{a_v}\Big]\log Z_t^{\le2k}\big(\omega_t^{B_t}(y,x),w\big)\neq0\implies\{v\in B_t:a_v>0\}\in\mathcal C_t.$$
--
--   Differences from the source:
--   - reading: T is the decomposition supplied by Theorem 1.1 → IsSec3Decomp G T k: rooted tree decomposition, adhesion at most 2k, bags (2k,k)-edge-unbreakable in G, at most max n 1 nodes, and nonempty bags when n > 0; reason: the setup on p. 15 uses the construction; pp. 23 and 35 bound its number of bags by n and p. 35 puts a vertex in each bag; at n = 0 use one empty bag; the size bound prevents an unbounded decomposition input at fixed n
--   - encoding: running time O*(·) on an unspecified machine → one deterministic TM2 machine (published OutputsWithin) and one constant C, both chosen before the instance, with the stated step bound in n = |V| and the parameter; reason: the paper names no machine model; O* suppresses factors polynomial in the input size, whose length is polynomial in n up to a log-of-parameter term absorbed by the exponential factor
--   - encoding: a family of size O*(2^{O(k)}), enumerated → encodeFamily L; C_t = L.toFinset with card ≤ C·2^{Ck}(n+1)^C, the same C; reason: one constant for all O-terms
--   - encoding: log over Q[[x, w, y]] → logPS of the polynomial omega (bag t) (Zle …) coerced to MvPowerSeries; reason: the same series
--   - generalization: the large-bag setting of Section 3.3, |B_t| > 4k+1 → no lower bound on the bag size; reason: large bags give the printed claim; for |B_t| ≤ 4k+1 the family of all subsets of size at most 2k has single-exponential size and contains every permitted support
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.3, p. 20, Lemma 3.3 (restated and proved p. 27)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.3, p. 20 (restated p. 27),
Lemma 3.3: for `G`, a decomposition `T` as supplied by Theorem 1.1 and a node `t`, one
machine enumerates within `C · 2^{C·k} · (n + 1)^C` steps a downward-closed family `C_t ⊆ 2^{B_t}`
of at most `C · 2^{C·k} · (n + 1)^C` sets, each of size at most `2k`, such that
`[x^b w^ℓ Π_{v ∈ B_t} y_v^{a_v}] log Z_t^{≤2k}(ω_t^{B_t}(y, x), w) ≠ 0` implies
`{v ∈ B_t : a_v > 0} ∈ C_t` whenever `ℓ ≤ k` and `|{v ∈ B_t : a_v > 0}| ≤ 2k`. -/
theorem lemma_3_3 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (T : RootedTD n) (t : Fin T.N),
        IsSec3Decomp G T k →
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (nodeInput G k T t) (encodeFamily L) (stepBound C k n) ∧
          (∀ D ∈ L, D ⊆ T.bag t ∧ D.card ≤ 2 * k) ∧
          (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧
          L.toFinset.card ≤ stepBound C k n ∧
          ∀ (b ℓ : ℕ) (a : Fin n → ℕ), ℓ ≤ k →
            ((T.bag t).filter (fun v => 0 < a v)).card ≤ 2 * k →
            MvPowerSeries.coeff
                (Finsupp.single Var.x b + Finsupp.single Var.w ℓ +
                  ∑ v ∈ T.bag t, Finsupp.single (Var.y v) (a v))
                (logPS ((omega (T.bag t) (Zle G (T.cone t) (T.bag t) k) :
                  MvPolynomial (Var n) ℚ) : MvPowerSeries (Var n) ℚ)) ≠ 0 →
            (T.bag t).filter (fun v => 0 < a v) ∈ L := by sorry

end SingleExpBisect.Main
