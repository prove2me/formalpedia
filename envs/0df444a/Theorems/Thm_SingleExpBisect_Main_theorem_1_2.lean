-- Prove2me | Theorems.Thm_SingleExpBisect_Main_theorem_1_2
-- name    : SingleExpBisect.Main.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:39:22.907481+00:00
-- url     : https://prove2.me/theorems/915a6150-d6fd-4550-8a07-66477d0a6ce9
-- title:
--   Theorem 1.2 — counting and recovering minimum bisections deterministically in 2^{O(k)}·n^{O(1)}
-- statement:
--   There are a constant $C$ and two deterministic machines $M_1,M_2$, fixed before the instance, such that for every simple graph $G$ on $n$ vertices and every integer $k\ge0$:
--
--   1. $M_1$ on input $(G,k)$ outputs, within $C\cdot2^{Ck}\cdot(n+1)^C$ steps, the number of sets $A\subseteq V(G)$ with $|A|=\lfloor n/2\rfloor$ and $|\delta_G(A)|\le k$ (each set counted once; $A$ and $V(G)\setminus A$ are different sets);
--   2. if such a set exists, $M_2$ on input $(G,k)$ outputs one such set within the same number of steps.
--
--   This is Minimum Bisection with parameter $k$: no hypothesis on $G$ (it may be disconnected or have $n\le1$) or on $k$.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph → SimpleGraph (Fin n) with vertex set Fin n; reason: Lean convention; every such graph is isomorphic to one on Fin n
--   - encoding: |A| = ⌊n/2⌋ → A.card = n / 2; reason: ℕ division is the floor
--   - encoding: counted and recovered "deterministically in O*(2^{O(k)}) time" → TM2 machines M₁, M₂ (published OutputsWithin) on the published encodeInput G k, outputs encodeNat (count) and encodeSet A, bound C·2^{C·k}·(n+1)^C, with C, M₁, M₂ chosen before n, G, k; reason: the paper names no machine; the input length is Θ(n² + log k), polynomial in n up to the log k term, which 2^{Ck} absorbs; n + 1 keeps the bound positive at n = 0
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §1.1, p. 4, Theorem 1.2 (restated and proved p. 23)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MinBisectFPT_cutSize
import Definitions.Def_MinBisectFPT_encodeCounts

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT ExponomialAssortment.FPTAS

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), p. 4, Theorem 1.2 (proof p. 23): "The
feasible solutions to Minimum Bisection can be counted deterministically in O∗(2^{O(k)}) time. If a
feasible solution exists, one can recover one within the same running time."

For one constant `C` and two machines fixed before the instance: on every simple graph `G` on
`n` vertices and every `k ≥ 0`, the first outputs the number of sets `A ⊆ V(G)` with
`|A| = ⌊n/2⌋` and `|δ_G(A)| ≤ k`, and, when such a set exists, the second outputs one; both within
`C · 2^{C·k} · (n + 1)^C` steps. -/
theorem theorem_1_2 :
    ∃ C : ℕ, ∃ M₁ M₂ : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ),
        HMBinPacking.OutputsWithin M₁ (encodeInput G k)
            (encodeNat ((Finset.univ : Finset (Finset (Fin n))).filter
              (fun A => A.card = n / 2 ∧ cutSize G A ≤ k)).card)
            (C * 2 ^ (C * k) * (n + 1) ^ C) ∧
          ((∃ A : Finset (Fin n), A.card = n / 2 ∧ cutSize G A ≤ k) →
            ∃ A : Finset (Fin n), A.card = n / 2 ∧ cutSize G A ≤ k ∧
              HMBinPacking.OutputsWithin M₂ (encodeInput G k) (encodeSet A)
                (C * 2 ^ (C * k) * (n + 1) ^ C)) := by sorry

end SingleExpBisect.Main
