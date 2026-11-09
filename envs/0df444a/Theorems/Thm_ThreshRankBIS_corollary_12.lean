-- Prove2me | Theorems.Thm_ThreshRankBIS_corollary_12
-- name    : ThreshRankBIS.corollary_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:12:43.542238+00:00
-- url     : https://prove2.me/theorems/5842bc28-727a-4643-9d65-dbf4b60f0f1a
-- title:
--   Corollary 12 — computable cutoff $T$ and global tail $Z_{\ge T}\le(\epsilon/4)Z_G(\lambda)$
-- statement:
--   Fix $0<\rho<1$ and $\lambda_0>0$, and let $a,c>0$ be the constants of (16). Let $G$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$, $d\ge1$, $k=k_\rho(G)$, and let $\mathcal C$ be a list of approximate cuts satisfying (7), $K=|\mathcal C|$. For $0<\epsilon\le1$ set
--
--   $$
--   T=\min\Bigl\{n+1,\Bigl\lceil\frac{v_d+\log(4K(n+1)^2/\epsilon)}{c}\Bigr\rceil\Bigr\},\qquad v_d=3ne^{-ad}. \tag{17}
--   $$
--
--   1. For every $d\ge1$ and $\lambda\ge\lambda_0$,
--   $$
--   Z_{\ge T}\le(\epsilon/4)\,q^n\le(\epsilon/4)\,Z_G(\lambda). \tag{18}
--   $$
--   2. For the randomized list with failure probability $\beta\in\{1/16,\epsilon/4\}$, whose size obeys Lemma 6's bound $K\le c_0\,2^{c_0k}(2n)^{c_0}\log(2/\beta)$, the cutoff satisfies $T=O_{\rho,\lambda_0}(k+ne^{-ad}+\log(n/\epsilon))$.
--   3. If $d\ge C_{\rho,\lambda_0}\log(n+1)$ for a sufficiently large constant, then $v_d\le1$ and $T=O_{\rho,\lambda_0}(k+\log(n/\epsilon))$.
--
--   The cutoff is computable from the list, and the tail it leaves is a quarter of the accuracy budget; its size controls the recovery work.
--
--   **Formalization Note** The $O$-statements are: for every $c_0>0$ there is $C_1>0$ depending only on $c_0,\rho,\lambda_0$ with $T\le C_1(\dots)$; in clause 3 the constant $C$ is chosen before $c_0$.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - generalization: the randomized list with failure probability 1/16 or ε/4 (of Lemma 6) → any list size K ≤ c₀·2^{c₀k}(2n)^{c₀}·log(2/β), β ∈ {1/16, ε/4}, for every constant c₀ > 0; reason: the order of T depends on the list only through its size, and the proof substitutes exactly Lemma 6's size bound 2^{O(k)} poly(N) log(2/β); Lemma 6's list is an instance
--   - encoding: T = O_{ρ,λ₀}(k + ne^{−ad} + log(n/ε)) → ∀ c₀ > 0 ∃ C₁ > 0 such that T ≤ C₁(k + ne^{−ad} + log(n/ε)) for every graph, ε, β and K as above; reason: the usual unfolding of the O-notation, with the constant independent of the graph and the inputs
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with the same lower bound; reason: the statement is about the combinatorial weights only and holds for every real λ in the range; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Corollary 12, p.15, displays (17)–(18); Lemma 6, p.9

import Mathlib
import Definitions.Def_ThreshRankBIS_SatisfiesEq7
import Definitions.Def_ThreshRankBIS_mWeight
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Corollary 12 (Computable cutoff and global tail)**, p.15. Fix `0 < ρ < 1`, `λ_0 > 0`. There
are constants `a, c > 0` (those of display (16)) such that:
1. for every `d`-regular bipartite `G` with `d ≥ 1`, every list `𝒞` satisfying (7), `K = |𝒞|`,
   every `λ ≥ λ_0` and `0 < ε ≤ 1`, the cutoff
   `T = min{n + 1, ⌈(v_d + log(4K(n + 1)²/ε))/c⌉}` (17), `v_d = 3ne^{−ad}`, satisfies
   `Z_{≥T} ≤ (ε/4)q^n ≤ (ε/4)Z_G(λ)` (18);
2. for the randomized list with failure probability `β ∈ {1/16, ε/4}`, whose size obeys Lemma 6's
   bound `K ≤ c_0 2^{c_0 k}(2n)^{c_0} log(2/β)`, `T = O_{ρ,λ_0}(k + ne^{−ad} + log(n/ε))`;
3. if `d ≥ C log(n + 1)` for a sufficiently large constant `C = C_{ρ,λ_0}`, then `v_d ≤ 1` and
   `T = O_{ρ,λ_0}(k + log(n/ε))`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Corollary 12, p.15;
Lemma 6, p.9 (the list-size bound).

**Formalization Note.** `k = k_ρ(G)` is `thresholdRank ρ E d`. In clauses 2–3, "the randomized
list" enters only through its size `K`, which is any natural number obeying Lemma 6's size bound
`2^{O(k)} poly(N) log(2/β)` with constant `c_0`; the `O`-constant `C_1` depends on `c_0, ρ, λ_0`
only. `C` is chosen before `c_0`. These clauses assume `n ≥ 1` (at `n = 0`, `log(n/ε) = log 0`
is a junk value). `λ, ε` are real. -/
theorem corollary_12 (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (lam0 : ℝ) (hlam0 : 0 < lam0) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      (∀ {n d : ℕ} (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
        ∀ 𝒞 : Finset (Finset (V n)), SatisfiesEq7 ρ E 𝒞 →
        ∀ lam : ℝ, lam0 ≤ lam → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          Ztail E (cutoffT n d #𝒞 a c ε) lam ≤ (ε / 4) * (1 + lam) ^ n ∧
            (ε / 4) * (1 + lam) ^ n ≤ (ε / 4) * hardcoreZ E lam) ∧
      (∀ c0 : ℝ, 0 < c0 → ∃ C1 : ℝ, 0 < C1 ∧
        ∀ {n d : ℕ} (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ β : ℝ, (β = 1 / 16 ∨ β = ε / 4) → ∀ K : ℕ,
          (K : ℝ) ≤ c0 * (2 : ℝ) ^ (c0 * thresholdRank ρ E d) * (2 * (n : ℝ)) ^ c0 *
            Real.log (2 / β) →
          (cutoffT n d K a c ε : ℝ) ≤
            C1 * (thresholdRank ρ E d + n * Real.exp (-(a * d)) + Real.log (n / ε))) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ c0 : ℝ, 0 < c0 → ∃ C1 : ℝ, 0 < C1 ∧
        ∀ {n d : ℕ} (E : Fin n → Fin n → Bool), IsRegular E d → 1 ≤ d → 0 < n →
          C * Real.log ((n : ℝ) + 1) ≤ d →
          3 * (n : ℝ) * Real.exp (-(a * d)) ≤ 1 ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ β : ℝ, (β = 1 / 16 ∨ β = ε / 4) → ∀ K : ℕ,
            (K : ℝ) ≤ c0 * (2 : ℝ) ^ (c0 * thresholdRank ρ E d) * (2 * (n : ℝ)) ^ c0 *
              Real.log (2 / β) →
            (cutoffT n d K a c ε : ℝ) ≤ C1 * (thresholdRank ρ E d + Real.log (n / ε))) := by sorry

end ThreshRankBIS
