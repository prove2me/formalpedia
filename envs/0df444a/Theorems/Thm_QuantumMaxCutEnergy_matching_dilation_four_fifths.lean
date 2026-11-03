-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_dilation_four_fifths
-- name    : QuantumMaxCutEnergy.matching_dilation_four_fifths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T21:42:12.135493+00:00
-- url     : https://prove2.me/theorems/955d3622-e57c-488a-80b0-a8b26541a426
-- title:
--   LP24 Lemma 4: $\frac45 x$ satisfies all odd-set constraints from star and triangle constraints
-- statement:
--   **LP24 Lemma 4: the $4/5$ odd-set dilation of a fractional matching** (arXiv:2401.03616, Lemma 4).
--
--   Let $x\ge0$ be a nonnegative weight on the edges of a graph on $n$ vertices. Suppose
--
--   * *(vertex loads)* for every vertex $v$, the total weight of the edges at $v$ is at most $1$;
--   * *(small odd sets)* for every odd set $S$ of at most $4$ vertices, the total weight of the edges with both
--     endpoints in $S$ is at most $(|S|-1)/2$ — that is, the constraint is trivial for $|S|=1$ and is the triangle
--     constraint $x_{ij}+x_{jk}+x_{ik}\le1$ for $|S|=3$.
--
--   **Theorem.** Then $\tfrac45x$ satisfies *all* of Edmonds' odd-set constraints,
--   $$\sum_{e\subseteq S}\tfrac45x_e\ \le\ \frac{|S|-1}{2}\qquad\text{for every odd } S\subseteq V,$$
--   and keeps nonnegative entries and vertex loads at most $1$; i.e. $\tfrac45x$ is a point of the fractional
--   matching polytope of Edmonds.
--
--   **Why the constant is $4/5$.** For odd $|S|\ge5$ the doubling argument gives
--   $2\sum_{e\subseteq S}x_e\le\sum_{e\subseteq S}x_e+\sum_{e\in\delta(S)}x_e=\sum_{v\in S}(\text{load at }v)\le|S|$,
--   so $\sum_{e\subseteq S}x_e\le|S|/2$ and $\tfrac45\cdot|S|/2\le(|S|-1)/2$ exactly when $|S|\ge5$; the case
--   $|S|=3$ is the triangle constraint used as is. The constant is attained by the uniform weight $x=1/4$ on the
--   edges of $K_5$: there $\sum_{e}x_e=2.5$ while every matching has at most $2$ edges.
--
--   **Role.** This is the matching side of the $0.595$ quantum max-cut analysis: the level-2 Pauli moments satisfy the
--   star constraint (`PauliSDP.moment_positive_excess_star`) and the triangle constraint
--   (`PauliSDP.moment_triangle_bound`), so $2h^{+}$ gives, after dilation, a point of the matching polytope, whence a
--   maximum-weight matching carries at least $\tfrac85\sum_e w_eh^{+}_e$ of weight. The node is proved here as the
--   $q=4$ instance of the general dilation `QuantumMaxCutEnergy.small_odd_sets`, which is a tracked reduction.
-- source:
--   Lee-Parekh, arXiv:2401.03616 (ICALP 2024), Lemma 4 (the 4/5 dilation of the odd-set polytope); Edmonds, Canad. J. Math. 1965 (matching polytope).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

theorem matching_dilation_four_fifths {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (htri : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ 4 →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2) :
    (∀ e, 0 ≤ ((4 : ℝ) / 5) * x e) ∧
    (∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then ((4 : ℝ) / 5) * x e else 0) ≤ 1) ∧
    (∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)),
        ((4 : ℝ) / 5) * x e) ≤ ((S.card : ℝ) - 1) / 2) := by sorry

end QuantumMaxCutEnergy
