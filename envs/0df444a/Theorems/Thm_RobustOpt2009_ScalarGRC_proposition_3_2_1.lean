-- Prove2me | Theorems.Thm_RobustOpt2009_ScalarGRC_proposition_3_2_1
-- name    : RobustOpt2009.ScalarGRC.proposition_3_2_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:41:43.533498+00:00
-- url     : https://prove2.me/theorems/885a8105-8784-4028-87f5-46e7e60a7eaa
-- title:
--   Proposition 3.2.1 — Globalized robustness equals nominal robustness and a unit-cone bound
-- statement:
--   Let $a^0,a^1,\ldots,a^L,x\in\mathbb R^n$ and $b^0,b^1,\ldots,b^L\in\mathbb R$. Let $Z\subseteq\mathbb R^L$ be nonempty, closed and convex, let $K\subseteq\mathbb R^L$ be a closed convex cone containing zero, fix any norm $N$ on $\mathbb R^L$, and let $\alpha\ge0$. For $\zeta\in Z+K$, define the constrained distance
--   $$d(\zeta,Z\mid K)=\inf\{N(\zeta-z):z\in Z,\ \zeta-z\in K\}.$$
--   Then $x$ satisfies the globalized robust counterpart
--   $$\left[a^0+\sum_{\ell=1}^L\zeta_\ell a^\ell\right]^Tx\le b^0+\sum_{\ell=1}^L\zeta_\ell b^\ell+\alpha d(\zeta,Z\mid K)\qquad(\forall\zeta\in Z+K)$$
--   if and only if both of the following hold:
--   1. $\left[a^0+\sum_{\ell=1}^L\zeta_\ell a^\ell\right]^Tx\le b^0+\sum_{\ell=1}^L\zeta_\ell b^\ell$ for every $\zeta\in Z$.
--   2. $\left[\sum_{\ell=1}^L\Delta_\ell a^\ell\right]^Tx\le\sum_{\ell=1}^L\Delta_\ell b^\ell+\alpha$ for every $\Delta\in K$ with $N(\Delta)\le1$.
--
--   This is Proposition 3.2.1: nominal robustness and a directional bound together characterize global robustness.
--
--   **Formalization Note** The book's cone $\mathcal L$ is named $K$ to distinguish it from the number $L$ of perturbation coordinates. An arbitrary norm is represented by a real seminorm with the explicit hypothesis $N(v)=0\Rightarrow v=0$. Coordinate sums use `Fin n` and `Fin L`, reindexed from the book's one-based notation, with the nominal coefficients stored separately. The real infimum is expanded in the statement and is used only when its set is nonempty; its values are bounded below by zero. Closedness refers to the usual finite-dimensional topology. Zero dimensions, $\alpha=0$, and the cone $\{0\}$ are allowed; no boundedness of $Z$ is assumed.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Proposition 3.2.1 and (3.2.1), printed p. 69 (PDF p. 95); standing hypotheses (G.a–c), Definition 3.1.1, (3.1.2)–(3.1.4), printed p. 68 (PDF p. 94); proof continues on printed p. 70 (PDF p. 96).

import Mathlib

open scoped BigOperators

namespace RobustOpt2009.ScalarGRC

/-- Proposition 3.2.1, with the perturbation structure of (G.a–c),
Ben-Tal, El Ghaoui and Nemirovski (2009), printed pp. 68–70 (PDF pp. 94–96).
The infimum is (3.1.3), evaluated only on Z + K. A definite real seminorm
represents the arbitrary norm of the source. Coordinates in Fin L are reindexed
from the book's 1,...,L; the nominal coefficients a0 and b0 are separate. -/
theorem proposition_3_2_1 {n L : ℕ}
    (a0 : Fin n → ℝ) (a : Fin L → Fin n → ℝ)
    (b0 : ℝ) (b : Fin L → ℝ)
    (Z K : Set (Fin L → ℝ)) (N : Seminorm ℝ (Fin L → ℝ))
    (hN : ∀ v, N v = 0 → v = 0)
    (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconvex : Convex ℝ Z)
    (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hKzero : (0 : Fin L → ℝ) ∈ K)
    (hKscale : ∀ (t : ℝ), 0 ≤ t → ∀ v ∈ K, t • v ∈ K)
    (α : ℝ) (hα : 0 ≤ α) (x : Fin n → ℝ) :
    (∀ ζ : Fin L → ℝ,
      (∃ z ∈ Z, ∃ d ∈ K, ζ = z + d) →
      (∑ j, (a0 j + ∑ l, ζ l * a l j) * x j) ≤
        b0 + (∑ l, ζ l * b l) +
          α * sInf {r : ℝ | ∃ z ∈ Z, ζ - z ∈ K ∧ r = N (ζ - z)}) ↔
    ((∀ ζ ∈ Z,
      (∑ j, (a0 j + ∑ l, ζ l * a l j) * x j) ≤ b0 + ∑ l, ζ l * b l) ∧
     (∀ d ∈ K, N d ≤ 1 →
      (∑ j, (∑ l, d l * a l j) * x j) ≤ (∑ l, d l * b l) + α)) := by sorry

end RobustOpt2009.ScalarGRC
