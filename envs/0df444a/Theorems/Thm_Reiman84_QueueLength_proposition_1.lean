-- Prove2me | Theorems.Thm_Reiman84_QueueLength_proposition_1
-- name    : Reiman84.QueueLength.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:48:52.938994+00:00
-- url     : https://prove2.me/theorems/f10da63e-b125-422c-ad4c-7e72f5353bb7
-- title:
--   Proposition 1 — U(x) is nonempty and has a unique least element
-- statement:
--   Let $P$ be a nonnegative $K\times K$ matrix with spectral radius strictly smaller than one. For $x\in D^K$ let
--   $$U(x)=\{y\in D^K_+ : x(t)+y(t)[I-P]\ge0\ \text{for all } t\},$$
--   where $D^K_+$ is the set of nonnegative, nondecreasing elements of $D^K$. Then $U(x)$ is nonempty and has a unique least element for the partial order $w\le w'$ iff $w_i(t)\le w'_i(t)$ for $0\le t\le1$, $1\le i\le K$.
--
--   The least element defines the map $f(x)=x+y(I-P)$, and Eq. (13) shows $Q=f(\tilde X)$.
--
--   **Formalization Note** Spectral radius $<1$ is stated as $P^m\to0$. Paths are compared, and the constraint defining $U(x)$ imposed, on $[0,1]$, the time domain of $D$; uniqueness of the least element is stated as equality on $[0,1]$.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 445, Proposition 1 (proof in the Appendix, pp. 457–458)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths

namespace Reiman84.QueueLength

open Filter Topology

/-- Proposition 1, p. 445: if `P` is nonnegative and has spectral radius strictly smaller than
unity (`Pᵐ → 0`), then for each `x ∈ D^K` the set `U(x)` is nonempty and has a unique least
element for the order `w ≤ w'` iff `wᵢ(t) ≤ w'ᵢ(t)` for `0 ≤ t ≤ 1`, `1 ≤ i ≤ K`. -/
theorem proposition_1 {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0))
    (x : ℝ → Fin K → ℝ) (hx : IsCadlag01 x) :
    (∃ y, InU P x y) ∧ (∃ y, IsLeastU P x y) ∧
    ∀ y y', IsLeastU P x y → IsLeastU P x y' → ∀ t ∈ Set.Icc (0 : ℝ) 1, y t = y' t := by sorry

end Reiman84.QueueLength
