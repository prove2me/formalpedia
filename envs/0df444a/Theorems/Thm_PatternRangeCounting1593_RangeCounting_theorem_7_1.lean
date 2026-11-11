-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_theorem_7_1
-- name    : PatternRangeCounting1593.RangeCounting.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:33.954613+00:00
-- url     : https://prove2.me/theorems/43e156af-f65d-446f-abd9-4fa8a9ebca40
-- title:
--   Theorem 7.1 — construction from a permutation
-- statement:
--   There is an absolute query constant $T$. Fix any permutation pattern $\pi$ and $K\ge2$. There are fixed constructor, dominance-query and rectangle-query programs, fixed component programs $Q$, constants $A,C,T_0,T_{idx},c_{KO},m_0$ and functions $e\ge0,r$ with $e(m)/m\to0$ and $r(m)/m\to0$, uniform over all inputs, with the following property.
--
--   For every length $m$, every explicit $\pi$-avoiding permutation $\tau$, and every admissible word size, the constructor produces one packed buffer $\beta_\tau$ and component offsets. It takes at most $Am+A$ steps and working words, including all shared-table generation, and
--   $$|\beta_\tau|\le Cm+C.$$
--   The same buffer supports exact dominance and inclusive rectangle queries for all cutoffs in $[0,m]$, including zero and empty intervals, within $T_0$ steps and within $T$ steps when $m\ge m_0$.
--
--   For $|\pi|\ge3$ it also satisfies
--   $$|\beta_\tau|\le2m\log_2s_\pi+r(m).$$
--   When $m\ge m_0$, it has the independently defined layout $\beta^{KO}\,N\,D\,J$: a retained representation, navigation directories, gateway index and boundary records for the same hierarchy and handles, meeting their operational specifications within $T_{idx}$ steps (the old rectangle counter within $c_{KO}$ times the logarithmic hierarchy bound). The additional bits satisfy
--   $$|N|+|D|+|J|\le e(m).$$
--   Short patterns and smaller inputs are included through direct representations; no hierarchy is required in those cases. The constructor starts only with the explicit permutation array, and queries start only with the constructed packed buffer and their register inputs.
--
--   This is the full construction clause of Theorem 1.1, expressed independently of that theorem and including its query and storage guarantees. **Formalization Note** The additive constants permit the empty input. Component offsets are constructor outputs, and the actual indexed buffer must fit the word-addressable interface domain.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - encoding: the representation in Theorem 1.1, with the construction in Section 7.1 → a constructed buffer with both exact query programs and all space bounds for every pattern and length; for |π| ≥ 3 above the threshold it additionally satisfies the independently defined IndexedRep contract; reason: direct representations cover the degenerate inputs described on printed p. 2; the hierarchy layout applies in its own asymptotic domain without narrowing the construction theorem
--   - encoding: linear time and working words, including shared-table generation → at most A·m + A steps and working words from the explicit permutation, producing all stored data and component offsets; reason: explicit uniform constants and an additive constant for m = 0
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 7.1, printed p. 23 (PDF p. 24), proof printed pp. 24–25 (PDF pp. 25–26)

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
import Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface
import Definitions.Def_PatternRangeCounting1593_RangeCounting_IndexSpecs
set_option autoImplicit false
open Filter Topology
open Classical

namespace PatternRangeCounting1593.RangeCounting

/-- Theorem 7.1 (Construction from a permutation). The constructor works for every pattern
and input length. In the nondegenerate asymptotic regime it produces the indexed layout of
Sections 4–5; direct representations handle the remaining inputs. Both query types and all
stored tables belong to the same constructed buffer. -/
theorem theorem_7_1 :
    ∃ T : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)) (K : ℕ), 2 ≤ K →
      ∃ (Q : RepProgs) (build domQ rectQ : Program) (A C T₀ Tidx cKO m₀ : ℕ)
        (e r : ℕ → ℝ),
        (∀ m, 0 ≤ e m) ∧
        Tendsto (fun m : ℕ => e m / m) atTop (𝓝 0) ∧
        Tendsto (fun m : ℕ => r m / m) atTop (𝓝 0) ∧
        ∀ m : ℕ, ∀ τ : Equiv.Perm (Fin m), Avoids π τ → ∀ w, WidthOK K m w →
          ∃ (bits : List Bool) (oN oD oJ : ℕ),
            BuildsWith w build (permMem τ) [m] ((A * m + A : ℕ) : ℝ)
              ((A * m + A : ℕ) : ℝ) bits [oN, oD, oJ] ∧
            bits.length ≤ C * m + C ∧
            (∀ x y, x ≤ m → y ≤ m →
              RunsQuery w domQ (packBits w bits) [m, bits.length, x, y] [Count τ x y] T₀ ∧
              (m₀ ≤ m →
                RunsQuery w domQ (packBits w bits) [m, bits.length, x, y] [Count τ x y] T)) ∧
            (∀ x₁ x₂ y₁ y₂, x₁ ≤ m → x₂ ≤ m → y₁ ≤ m → y₂ ≤ m →
              RunsQuery w rectQ (packBits w bits) [m, bits.length, x₁, x₂, y₁, y₂]
                [rectCount τ x₁ x₂ y₁ y₂] T₀ ∧
              (m₀ ≤ m →
                RunsQuery w rectQ (packBits w bits) [m, bits.length, x₁, x₂, y₁, y₂]
                  [rectCount τ x₁ x₂ y₁ y₂] T)) ∧
            (3 ≤ k →
              (bits.length : ℝ) ≤ 2 * m * Real.logb 2 (swLimit π) + r m ∧
              (m₀ ≤ m →
                IndexedRep π w τ Q Tidx cKO bits oN oD oJ ∧
                ((bits.length - oN : ℕ) : ℝ) ≤ e m)) := by sorry

end PatternRangeCounting1593.RangeCounting
