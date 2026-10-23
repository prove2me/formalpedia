-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_theorem_2
-- name    : SaturatedNet.Uniqueness.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:54.087983+00:00
-- url     : https://prove2.me/theorems/d54b3ff4-2028-45f4-a508-58d4217cbdbb
-- title:
--   Theorem 2, p. 16 — for ρ(P) ≤ 1, equilibria are unique on classes with ρ < 1, and on classes with ρ = 1 non-unique iff (35)–(36), forming the segment (37)
-- statement:
--   Let $(P, w)$ be a network ($P \ge 0$, $w \ge 0$) with $\rho(P) \le 1$, and $c$ any exogenous flow.
--   Let $\mathcal V_l$ be a class of $P$ (a strongly connected component of $\mathcal G_P$) with
--   principal block $P^{(ll)}$, and fix a network equilibrium $x$. Consider the set of projections
--   $x'^{(l)}$ on $\mathcal V_l$ of all network equilibria $x'$ that coincide with $x$ on the nodes
--   upstream of $\mathcal V_l$ (the paper's "given $(x^{(1)}, \dots, x^{(l-1)})$"), and write
--
--   $$u^{(l)} = c^{(l)} + \sum_{1 \le i < l} P^{(il)\top}x^{(i)}, \qquad u^{(l)}_j = c_j + \sum_{k \notin \mathcal V_l} P_{kj}x_k .$$
--
--   1. If $\rho(P^{(ll)}) < 1$, the projection is unique: the set is $\{x^{(l)}\}$.
--   2. If $\rho(P^{(ll)}) = 1$, let $p^{(l)}$ and $\pi^{(l)}$ be right and left dominant eigenvectors of
--      $P^{(ll)}$ (nonnegative, nonzero, $P^{(ll)}p^{(l)} = p^{(l)}$, $\pi^{(l)\top}P^{(ll)} = \pi^{(l)\top}$).
--      The projection is non-unique if and only if
--      $$p^{(l)\top}u^{(l)} = 0 \quad\text{and}\quad \min_{i \in \mathcal V_l}\Big\{\frac{\nu^{(l)}_i}{\pi^{(l)}_i}\Big\} + \min_{i \in \mathcal V_l}\Big\{\frac{w_i - \nu^{(l)}_i}{\pi^{(l)}_i}\Big\} > 0$$
--      for a solution $\nu^{(l)}$ of $\nu^{(l)} = P^{(ll)\top}\nu^{(l)} + u^{(l)}$ ((35)–(36)). In that
--      case, for every such solution $\nu^{(l)}$, the set of projections is exactly
--      $$\Big\{\nu^{(l)} + \alpha\pi^{(l)} :\ -\min_{i \in \mathcal V_l}\Big\{\frac{\nu^{(l)}_i}{\pi^{(l)}_i}\Big\} \le \alpha \le \min_{i \in \mathcal V_l}\Big\{\frac{w_i - \nu^{(l)}_i}{\pi^{(l)}_i}\Big\}\Big\} \qquad (37).$$
--
--   Applied class by class along the block-triangular order (14), this describes the whole lattice of
--   equilibria $\mathcal X$ of a network with $\rho(P) \le 1$: unique on the classes of spectral radius
--   below one, and a segment, or a point, on each class of spectral radius one.
--
--   **Formalization Note.** The statement is permutation-free: instead of assuming $P$ in block
--   triangular form, it quantifies over a class $V$ and fixes the equilibrium on the nodes upstream of
--   $V$ (outside $V$, with a path into $V$). Fixing every earlier class of a compatible ordering gives
--   the same set of projections, since earlier classes that are not upstream neither feed nor are fed by
--   $V$. The equilibria $x'$ range over equilibria of the *whole* network. The third bullet of the paper
--   prints $\nu^{(l)} = P^{(ll)\top}\nu^{(l)} + \sum_{i=1}^{l} P^{(jl)\top}x^{(i)} + c^{(l)}$, a slip for
--   the sum over $i < l$ used here (compare (35) and (38)). As in Proposition 5, "any solution
--   $\nu^{(l)}$" is an existential in the equivalence and a universal in (37), and (37) is stated as an
--   equality of sets (the proof reduces to Proposition 5, (30)). The hypothesis $\rho(P) \le 1$ ensures
--   every class falls under case 1 or 2.
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 16, Theorem 2, (34)–(37)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem theorem_2 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hρ : specRad P ≤ 1)
    (V : Finset n) (hV : IsClass P V) (x : n → ℝ) (hx : x ∈ equilibria P w c) :
    (specRad (block P V) < 1 → classProj P w c V x = {fun i : V => x i}) ∧
    (specRad (block P V) = 1 →
      ∀ p π : V → ℝ, 0 ≤ p → p ≠ 0 → block P V *ᵥ p = p →
        0 ≤ π → π ≠ 0 → π ᵥ* block P V = π →
        ((classProj P w c V x).Nontrivial ↔
          (p ⬝ᵥ classInflow P c V x = 0 ∧
            ∃ ν : V → ℝ, ν = ν ᵥ* block P V + classInflow P c V x ∧
              minRatio ν π hV.univ_nonempty +
                minRatio (fun i : V => w i - ν i) π hV.univ_nonempty > 0)) ∧
        ((classProj P w c V x).Nontrivial →
          ∀ ν : V → ℝ, ν = ν ᵥ* block P V + classInflow P c V x →
            classProj P w c V x =
              {z | ∃ α : ℝ, -minRatio ν π hV.univ_nonempty ≤ α ∧
                α ≤ minRatio (fun i : V => w i - ν i) π hV.univ_nonempty ∧
                z = ν + α • π})) := by sorry

end SaturatedNet.Uniqueness
