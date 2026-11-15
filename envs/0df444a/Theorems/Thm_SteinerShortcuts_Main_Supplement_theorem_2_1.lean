-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_Supplement_theorem_2_1
-- name    : SteinerShortcuts.Main.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:40:43.876087+00:00
-- url     : https://prove2.me/theorems/e2ef0fae-dd31-4cbe-bc25-6159cf8febd3
-- title:
--   Theorem 2.1 — layered DAGs forcing m^{1+δ} added edges or n^δ diameter, δ = 1/30063
-- statement:
--   Let $G_k=(V_k,E_k)$, $k\ge 0$, be the fixed family of finite directed graphs of the mission's construction (§3.2, with $L_k=2k+4$ layers and a prime $q_k\in[L_k,2L_k]$), with $n_k=|V_k|$ vertices and $m_k=|E_k|$ edges. A **Steiner shortcut** of $G_k$ adds a finite set $V^+$ of new vertices and a finite set $E^+$ of new edges on $V_k\cup V^+$, such that for all original vertices $u,v$, $v$ is reachable from $u$ in $G_k$ if and only if it is reachable in the augmented graph $G^+$. The diameter $\operatorname{diam}(G^+)$ is the largest finite hop distance between any two vertices of $G^+$, original or Steiner. Put
--   $$
--   \delta=\frac{1}{30063}.
--   $$
--   The theorem asserts three things.
--
--   1. The family is infinite in the strong sense that $n_k\to\infty$.
--   2. Every $G_k$ is layered: there is a map $\ell:V_k\to\mathbb N$ with $\ell(v)=\ell(u)+1$ for every edge $(u,v)\in E_k$; in particular $G_k$ is acyclic.
--   3. There are constants $c_E>0$, $c_D>0$ and an index $k_0$, chosen before $k$ and before the augmentation, such that for every $k\ge k_0$ and every Steiner shortcut $G^+=(V_k\cup V^+,E_k\cup E^+)$ of $G_k$,
--   $$
--   |E^+|\ \ge\ c_E\, m_k^{1+\delta}\qquad\text{or}\qquad \operatorname{diam}(G^+)\ \ge\ c_D\, n_k^{\delta}.
--   $$
--
--   This is the paper's first refutation of the Steiner shortcut conjecture: no Steiner shortcutting with almost-linearly many added edges can reduce the diameter of these layered DAGs below a fixed polynomial in $n$. The mission's goal (Theorem 1.3) improves the exponent from $1/30063$ to $1/56-O(\varepsilon)$ for budgets $O(m^{1+\varepsilon})$.
--
--   **Formalization Note** The exponent $\delta=1/30063$ is the one the paper derives for its §2 construction (printed p. 14, footnote 3: $k=1430$, $K=33+21k=30063$, $\delta=1/K$). The two $\Omega$'s are resolved by absolute positive constants $c_E,c_D$ and a threshold $k_0$, uniform over the member and the augmentation. The witness family is the published optimized family `familyGraph` of the base mission, not the degree-four family of §2; the source theorem only asserts existence of a family. New vertices are an arbitrary finite type $W$, with vertex type $V_k\oplus W$; added edges may coincide with original ones, which only enlarges $|E^+|$.
--
--   Differences from the source:
--   - generalization: there exist an absolute δ>0 and some infinite family of layered DAGs → δ = 1/30063 fixed and the specific published family familyGraph k; reason: a concrete δ and a concrete witness family imply the existential statement; 1/30063 is the value the paper itself derives (footnote 3)
--   - reading: an infinite family with |E⁺| = Ω(m^{1+δ}) or diam(G⁺) = Ω(n^δ) → n_k → ∞, and positive c_E, c_D, k₀ fixed before k and the augmentation with c_E m_k^{1+δ} ≤ |E⁺| ∨ c_D n_k^δ ≤ diam for all k ≥ k₀; reason: the standard uniform reading of both Ω's over the family; the tail k ≥ k₀ is the asymptotic family
--   - encoding: (layered) DAGs → a natural-number layer map increasing by exactly one along every edge; reason: this is the definition of layered and implies acyclicity
--   - encoding: new vertices V⁺ disjoint from V and new edges E⁺ → every finite type W with vertex type V⊕W, and a finite arc set on V⊕W that may overlap embedded original arcs; reason: every disjoint finite augmentation is represented; overlapping arcs leave the augmented graph unchanged and only enlarge |E⁺|
--   - encoding: diam(G⁺) → the largest finite hop distance over all ordered pairs of V⊕W, 0 if none; reason: the base mission's published diameter; unreachable pairs do not contribute
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 4, Theorem 2.1; restated p. 13, proof pp. 13–14, δ = 1/30063 from footnote 3 on p. 14 (PDF pp. 6, 15–16)

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main.Supplement

/-- Theorem 2.1 with the paper's exponent δ = 1/30063, witnessed by the published
layered family: the family grows, every member is layered (hence a DAG), and there
are absolute positive constants and a threshold, fixed before the member and the
augmentation, such that every finite Steiner shortcut has at least `c_E·m^{1+δ}`
added edges or diameter at least `c_D·n^δ`. -/
theorem theorem_2_1 :
    Filter.Tendsto (fun k : ℕ => (Fintype.card (FamilyVertex k) : ℝ))
      Filter.atTop Filter.atTop ∧
    (∀ k : ℕ, ∃ layer : FamilyVertex k → ℕ, IsLayered (familyGraph k) layer) ∧
    ∃ cE : ℝ, 0 < cE ∧ ∃ cD : ℝ, 0 < cD ∧ ∃ k₀ : ℕ,
      ∀ k : ℕ, k₀ ≤ k → ∀ (W : Type) [Fintype W],
      ∀ extra : Finset ((FamilyVertex k ⊕ W) × (FamilyVertex k ⊕ W)),
        IsSteinerShortcut (familyGraph k) extra →
        cE * Real.rpow ((edgeSet (familyGraph k)).card : ℝ) (1 + 1/30063) ≤
            (extra.card : ℝ) ∨
          cD * Real.rpow (Fintype.card (FamilyVertex k) : ℝ) (1/30063) ≤
            (diameter (augment (familyGraph k) extra) : ℝ) := by sorry

end SteinerShortcuts.Main.Supplement
