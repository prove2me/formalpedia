-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_steiner_shortcut_lower_bound
-- name    : SteinerShortcuts.Main.steiner_shortcut_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:24.985166+00:00
-- url     : https://prove2.me/theorems/c654a21e-eaf6-4ab8-96d3-ec2d5c9507bd
-- title:
--   Theorem 1.3 — polynomial lower bounds for arbitrary Steiner shortcuts
-- statement:
--   There is a fixed sequence of finite directed graphs $G_k=(V_k,E_k)$, with $n_k=|V_k|\to\infty$ and $m_k=|E_k|$, such that for every $\varepsilon>0$ and $A>0$ there are $b>0$ and $k_0$ for which, for every $k\ge k_0$ and every finite Steiner shortcut $G^+$ of $G_k$,
--   $$
--   |E^+|\le A m_k^{1+\varepsilon}\quad\Longrightarrow\quad
--   \operatorname{diam}(G^+)\ge b n_k^{(1-57\varepsilon)/56}.
--   $$
--   The family is chosen before $\varepsilon,A$. The constants $b,k_0$ depend only on these two parameters and are uniform over $k$ and the entire augmentation. Diameter is the largest finite hop distance over original and Steiner vertices. The statement permits every finite new vertex set and every reachability-preserving added edge set, without a DAG or layering assumption on the augmentation.
--
--   **Formalization Note** The witness uses $L_k=2k+4$ and the least admissible prime fixed for each $L_k$. The positive prefactor and the exponent loss $57\varepsilon/56$ resolve the asymptotic notation using the paper's final calculation on PDF page 26. This retains the exponent $1/56$; no smaller target is substituted.
--
--   Differences from the source:
--   - reading: an infinite family, |E⁺|=O(m^{1+ε}) and diameter n^{1/56−O(ε)} → n_k tends to infinity, every positive budget factor A, and b n_k^{(1−57ε)/56} for b>0 beyond k₀(ε,A); reason: eq. (11) and the proof give m=Θ(n^{57/56}) and D=Ω(Lm/(|E⁺|+m)); the family precedes ε,A and the constants precede k and the augmentation
--   - encoding: the explicit construction used to witness the existential family → L_k=2k+4, the least prime in [L_k,2L_k], and the finite subtype of actual coordinate vertices; reason: even L≥4 sees both parities; the prime choice is fixed independently of the budget and removes no asymptotic instance
--   - encoding: new vertices V⁺ disjoint from V, and arbitrary added edges → all finite W with vertex type V⊕W; E⁺ may overlap embedded E; reason: every disjoint finite augmentation is represented; overlapping arcs merely enlarge the counted budget without changing the augmented graph
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 2, Theorem 1.3; proof pp.23–24 (PDF pp.25–26) (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main

/-- Theorem 1.3 with the fixed construction, the proof's loss 57ε/56,
and a positive prefactor and threshold depending only on ε and A. -/
theorem steiner_shortcut_lower_bound :
    Filter.Tendsto (fun k : ℕ => (Fintype.card (FamilyVertex k) : ℝ))
      Filter.atTop Filter.atTop ∧
    ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ k₀ : ℕ,
      ∀ k : ℕ, k₀ ≤ k → ∀ (W : Type) [Fintype W],
      ∀ extra : Finset ((FamilyVertex k ⊕ W) × (FamilyVertex k ⊕ W)),
        IsSteinerShortcut (familyGraph k) extra →
        (extra.card : ℝ) ≤ A * Real.rpow ((edgeSet (familyGraph k)).card : ℝ) (1+ε) →
        b * Real.rpow (Fintype.card (FamilyVertex k) : ℝ) ((1-57*ε)/56) ≤
          (diameter (augment (familyGraph k) extra) : ℝ) := by sorry

end SteinerShortcuts.Main
