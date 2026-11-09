-- Prove2me | Theorems.Thm_SignRankMargin_OREquality_lemma_12
-- name    : SignRankMargin.OREquality.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:42:34.933573+00:00
-- url     : https://prove2.me/theorems/362dc39d-e22d-4cac-999b-ba4546cf70a3
-- title:
--   Lemma 12 — exceptional sets for positive inner products
-- statement:
--   Let $F:X\times Y\to\{0,1\}$ be a Boolean matrix on finite nonempty sets, with at most $\eta|X||Y|$ ones, where $0<\eta<1$. Let $u_x,v_y\in\mathbb R^r$ be any unit-vector realization of $F$ and put $H(x,y)=\langle u_x,v_y\rangle$. For every $0<\tau<1$, there exist subsets $E\subseteq X$ and $G\subseteq Y$ with
--
--   $$
--   \frac{|E|}{|X|}+\frac{|G|}{|Y|}\le2\sqrt{\eta(1+4/\tau)^r}
--   $$
--
--   and
--
--   $$
--   0<H(x,y)\le\tau\quad\text{whenever }F(x,y)=1,\ x\notin E,\ y\notin G.
--   $$
--
--   The dimension and realization are arbitrary. This milestone controls all surviving positive entries while bounding the sum of both exceptional fractions.
--
--   Differences from the source:
--   - encoding: finite nonempty sets X,Y and subsets E,G → Fintype and Nonempty instances for X,Y, and Finset subsets E,G; reason: every subset of a finite set has exactly this finite representation; denominators remain positive
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Lemma 12, p. 11; proof p. 12

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_Geometry

namespace SignRankMargin.OREquality

/-- Lemma 12, p.11: the two exceptional fractions add and every surviving positive entry is small. -/
theorem lemma_12 {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : Matrix X Y Bool) (η : ℝ) (hηpos : 0 < η) (hηlt : η < 1)
    (hsparse : (oneCount F : ℝ) ≤ η * (Fintype.card X : ℝ) * (Fintype.card Y : ℝ))
    (r : ℕ) (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r))
    (hreal : UnitRealization F r u v) (τ : ℝ) (hτpos : 0 < τ) (hτlt : τ < 1) :
    ∃ (E : Finset X) (G : Finset Y),
      (E.card : ℝ) / (Fintype.card X : ℝ) +
        (G.card : ℝ) / (Fintype.card Y : ℝ) ≤
        2 * Real.sqrt (η * (1 + 4 / τ) ^ r) ∧
      ∀ x y, F x y = true → x ∉ E → y ∉ G →
        0 < inner ℝ (u x) (v y) ∧ inner ℝ (u x) (v y) ≤ τ := by sorry

end SignRankMargin.OREquality
