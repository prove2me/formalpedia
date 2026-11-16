-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_corollary_4_9
-- name    : RoundedPotentials.Main.Supplement.corollary_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:09:55.619047+00:00
-- url     : https://prove2.me/theorems/0f5cc1a7-1392-4aea-942a-c668adb5fe4d
-- title:
--   Corollary 4.9 — All pairs
-- statement:
--   Let
--   $$\gamma=\min_{0\le\beta\le1}\max\{\omega(3-\beta,1,1),\,3+\beta\},$$
--   where $\omega(a,b,c)$ is the exponent of multiplying an $n^a\times n^b$ by an $n^b\times n^c$ matrix. Fix an exponent $D$ and $\varepsilon>0$.
--
--   There are a deterministic program and constants $C,K$ with the following property. For every $n\ge2$, every $1\le W\le n^D$ and every capacity matrix with entries at most $W$, consider one block for every ordered pair of distinct vertices, each with a claim in $[0,(n-1)W]$ and grid indices in $[0,(2n-1)Q_0]$. The program performs all excess tests within $Cn^{\gamma+\varepsilon}+C$ steps. In other words, the excess tests for the set of all ordered pairs take $n^{\gamma+o(1)}$ time.
--
--   With published bounds on $\omega(2,1,1)$ and $\omega(2.5,1,1)$ this gives $\gamma<3.614$, and if $\omega=2$ then $\gamma=7/2$.
--
--   **Formalization Note** $\omega(a,b,c)$ is the published operational exponent `omega3` on the same word RAM: the infimum of the $\tau$ for which, for every $\varepsilon>0$, a deterministic program multiplies in $O(N^{\tau+\varepsilon})$ steps. $\gamma$ is the infimum over $\beta\in[0,1]$.
--
--   Differences from the source:
--   - generalization: ω(a, b, c), the exponent of rectangular matrix multiplication → the published operational exponent omega3 on the word RAM DynConnWC.Program; reason: the source's §2 defines it as the exponent of multiplying; the operational exponent is at most the algebraic one, so a time bound n^{γ+ε} with this γ implies the bound with the algebraic γ
--   - encoding: min over 0 ≤ β ≤ 1 → sInf over β ∈ [0, 1]; reason: a nonempty set bounded below by 3; equal to the minimum when it is attained
--   - encoding: n^{γ+o(1)} time → for every ε > 0 a deterministic program and C with at most C·n^{γ+ε} + C steps; reason: the meaning of o(1) in the exponent (§2: running times hide n^{o(1)} factors)
--   - encoding: the excess tests for the set of all ordered pairs → pass bits for one block per ordered pair of distinct vertices, in lexicographic order, with 0 ≤ p ≤ (n−1)W and indices in [0, (2n−1)Q₀]; ∀ D, W ≤ n^D; reason: the setting of Lemma 4.8 for all pairs; standing polynomial bound
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 24, Corollary 4.9

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Verification

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main DynConnWC MinKCutII.Main MultStretchAPASP.Weighted

theorem corollary_4_9 (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : Program, IsDeterministic Q ∧ ∃ C K : ℕ,
      ∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D →
      ∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
      ∀ (bs : List (Block n)), bs.map (fun b => (b.s, b.t)) = distinctPairs n →
        (∀ b ∈ bs, BlockPromise n W b) →
          let x := allPairsInput n W cap bs
          let T : ℝ := C * (n : ℝ) ^ (gammaExp + ε) + C
          let Wd := wordSize K x T
          ∀ ω : ℕ → Fin (2 ^ Wd),
            HaltsWithin Wd Q x ω T ∧ finalOutput Wd Q x ω = excessAnswers n W cap bs := by sorry

end RoundedPotentials.Main.Supplement
