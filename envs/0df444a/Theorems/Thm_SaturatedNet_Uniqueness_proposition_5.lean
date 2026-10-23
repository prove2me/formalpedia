-- Prove2me | Theorems.Thm_SaturatedNet_Uniqueness_proposition_5
-- name    : SaturatedNet.Uniqueness.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:44.775262+00:00
-- url     : https://prove2.me/theorems/6ae44886-415f-4bdd-a37b-ee064f4bbfde
-- title:
--   Proposition 5, p. 14 — for irreducible P with ρ(P) = 1, equilibria are non-unique iff pᵀc = 0 and (29), and then form the segment (30)
-- statement:
--   Let $(P, w)$ be a network with $P$ irreducible and $\rho(P) = 1$, on $n \ge 1$ nodes. Let $p$ and
--   $\pi$ be right and left dominant eigenvectors of $P$: nonnegative, nonzero, $Pp = p$ and
--   $\pi^\top P = \pi^\top$. Then, for every exogenous flow $c$, there is more than one network
--   equilibrium if and only if
--
--   $$p^\top c = 0, \qquad \min_i\Big\{\frac{\nu_i}{\pi_i}\Big\} + \min_i\Big\{\frac{w_i - \nu_i}{\pi_i}\Big\} > 0,$$
--
--   where $\nu$ is a solution of $\nu = P^\top \nu + c$. Moreover, in this case, for any such solution
--   $\nu$, the set of network equilibria is the segment
--
--   $$\mathcal X = \Big\{ x = \nu + \alpha\pi :\ -\min_i\Big\{\frac{\nu_i}{\pi_i}\Big\} \le \alpha \le \min_i\Big\{\frac{w_i - \nu_i}{\pi_i}\Big\}\Big\}.$$
--
--   This is the irreducible critical case; Theorem 2 applies it to each class whose block has spectral
--   radius one, with the exogenous flow coming from the upstream classes.
--
--   **Formalization Note.** "More than one equilibrium" is `Set.Nontrivial`. The paper's "$\nu$ is any
--   solution" is encoded by an existential in the equivalence and a universal in the description of
--   $\mathcal X$; the value of the left-hand side of (29) does not depend on the solution chosen, since
--   two solutions differ by a multiple of $\pi$. The node type is assumed nonempty so that the minima
--   are taken over a nonempty set. Positivity of $\pi$ is not assumed: it follows from Proposition 2 (iii).
-- source:
--   Massai, Como & Fagnani, Equilibria and Systemic Risk in Saturated Networks, arXiv:1912.04815v2, p. 14, Proposition 5, (29)–(30)

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix

namespace SaturatedNet.Uniqueness

theorem proposition_5 {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) [Nonempty n]
    (hirr : IsIrreducible P) (hρ : specRad P = 1)
    (p π : n → ℝ) (hp0 : 0 ≤ p) (hp : p ≠ 0) (hpP : P *ᵥ p = p)
    (hπ0 : 0 ≤ π) (hπ : π ≠ 0) (hπP : π ᵥ* P = π) :
    ((equilibria P w c).Nontrivial ↔
      (p ⬝ᵥ c = 0 ∧ ∃ ν : n → ℝ, ν = ν ᵥ* P + c ∧
        minRatio ν π Finset.univ_nonempty + minRatio (w - ν) π Finset.univ_nonempty > 0)) ∧
    ((equilibria P w c).Nontrivial →
      ∀ ν : n → ℝ, ν = ν ᵥ* P + c →
        equilibria P w c =
          {x | ∃ α : ℝ, -minRatio ν π Finset.univ_nonempty ≤ α ∧
            α ≤ minRatio (w - ν) π Finset.univ_nonempty ∧ x = ν + α • π}) := by sorry

end SaturatedNet.Uniqueness
