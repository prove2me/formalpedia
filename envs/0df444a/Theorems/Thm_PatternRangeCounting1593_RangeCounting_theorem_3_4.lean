-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_theorem_3_4
-- name    : PatternRangeCounting1593.RangeCounting.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:12.595511+00:00
-- url     : https://prove2.me/theorems/c1a4c487-578a-4368-ad11-2ccbba3af265
-- title:
--   Theorem 3.4 — the Kozma–Opler interface (K1)–(K4)
-- statement:
--   Fix a pattern $\pi$ with $|\pi|\ge 3$ and a width parameter $K\ge2$. There is an absolute constant $T$ (independent of $\pi$ and $K$) such that, for fixed operation programs and a fixed construction program depending only on $\pi$ and $K$, and for every $\pi$-avoiding permutation $\tau$ of length $m$ above a threshold $m_0(\pi,K)$ and every admissible word size $w$:
--
--   1. the construction program builds, from the explicit permutation, within $A\,m$ steps, a bit string $\beta$ of length
--   $$|\beta|\le 2m\log_2 s_\pi+r(m),\qquad r(m)/m\to0;$$
--   2. $\beta$ is a retained Kozma–Opler representation of $\tau$ for some hierarchy and handle encoding: (K1) nested row and column divisions at levels $0,\dots,\ell$, the root division trivial, $m_i$ blocks per axis at level $i$ with $L=\lfloor m/\sqrt{\log_2 m}\rfloor$, $\omega_0=m$, $\omega_{i+1}=\lfloor\omega_i^{5/6}\rfloor$, $\ell$ least with $m/\omega_\ell\ge L$, $m_i=\lfloor m/\omega_i\rfloor$ for $i<\ell$, $m_\ell=L$, every level-$i$ block of size at most $40m/m_i$; (K2) every block meets at most $\Delta=\lceil10c_\pi\rceil$ occupied cells; (K3) the navigation operations (finest block of a coordinate with its endpoints and offset, child handle from a parent handle and one-based child index, tree parent/child/leaf selection, childRank, leafRank, rank and select on the coordinate bitvector) and (K4) the local queries all run within $T$ steps; the exact rectangle counter runs within $c_{KO}(\lfloor\log_2\lfloor\log_2 m\rfloor\rfloor+1)$ steps;
--   3. the parameters satisfy Equation (4): there are $c_1,c_2>0$ with, for $m\ge m_0$,
--   $$c_1\log\log m\le\ell\le c_2\log\log m,\quad c_1\frac{m}{\sqrt{\log m}}\le L\le c_2\frac{m}{\sqrt{\log m}},\quad H\le c_2L\ell,$$
--   and $H/m\to0$.
--
--   This is the retained structure on which the additional index of the paper is built; it is a cited result of Kozma and Opler, recorded here as the first milestone.
--
--   **Formalization Note** $O_\pi(m)$ construction time is $A\,m$ steps with $A$ depending on $\pi,K$; $o_\pi(m)$ is a function $r$ with $r(m)/m\to0$; logarithms are base two. The construction clause carries no working-word bound, as in the source.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - reading: the (K3)/(K4) operations take constant time → one absolute constant T, chosen before π and K, bounds every operation above the threshold; reason: §3.1 convention: for each fixed parameter choice the query operations take an absolute constant number of word operations on sufficiently large inputs; the paper's absolute query bound relies on it
--   - reading: a block handle consists of its succinct-tree node identifier and its local-counter address, a constant number of words → two words; node identifiers injective on the blocks of an axis and below 2·(number of tree nodes)+2; reason: range of a balanced-parenthesis or LOUDS position of a succinct tree
--   - encoding: the representation supplies the operations → fixed programs, read-only, correct on every buffer of fewer than 2^w bits beginning with the representation, with the register layouts of Def_KOInterface; the base buffer itself has fewer than 2^w bits; reason: makes the operations usable as subroutines when the index is appended; the explicit size condition ensures the contract checks the base itself
--   - encoding: Θ(log log m), Θ(m/√log m), H = O(Lℓ) = o(m) in (4) → explicit constants c₁, c₂ > 0 above m₀ and H/m → 0; reason: standard reading of the asymptotic notation
--   - encoding: block size at most 40m/m_i → |B|·m_i ≤ 40m; reason: same inequality without real division
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 3.4, printed pp. 11–12 (PDF pp. 12–13), with the local-query conventions of printed pp. 12–13 (PDF pp. 13–14); attributed to Kozma–Opler, arXiv:2510.20382v1, Lemma 2.2, Section 4, Theorem 1.3

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

/-- Theorem 3.4 (Kozma–Opler interface [KO26, Lemma 2.2 and Section 4]). -/
theorem theorem_3_4 :
    ∃ T : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)), 3 ≤ k → ∀ K : ℕ, 2 ≤ K →
      ∃ (P : KOProgs) (build : Program) (cKO A m₀ : ℕ) (r : ℕ → ℝ) (c₁ c₂ : ℝ),
        Tendsto (fun m : ℕ => r m / m) atTop (𝓝 0) ∧
        0 < c₁ ∧ 0 < c₂ ∧
        (∀ m ≥ m₀,
          c₁ * Real.logb 2 (Real.logb 2 m) ≤ depth m ∧
          (depth m : ℝ) ≤ c₂ * Real.logb 2 (Real.logb 2 m) ∧
          c₁ * ((m : ℝ) / Real.sqrt (Real.logb 2 m)) ≤ finestCount m ∧
          (finestCount m : ℝ) ≤ c₂ * ((m : ℝ) / Real.sqrt (Real.logb 2 m)) ∧
          (Hsum m : ℝ) ≤ c₂ * finestCount m * depth m) ∧
        Tendsto (fun m : ℕ => (Hsum m : ℝ) / m) atTop (𝓝 0) ∧
        ∀ m ≥ m₀, ∀ τ : Equiv.Perm (Fin m), Avoids π τ → ∀ w, WidthOK K m w →
          ∃ (bits : List Bool) (Hd : Hierarchy) (hdl : Handles),
            (∃ W : ℝ, BuildsWith w build (permMem τ) [m] ((A * m : ℕ) : ℝ) W bits []) ∧
            (bits.length : ℝ) ≤ 2 * m * Real.logb 2 (swLimit π) + r m ∧
            KOInterface π w τ P T cKO bits Hd hdl := by sorry

end PatternRangeCounting1593.RangeCounting
