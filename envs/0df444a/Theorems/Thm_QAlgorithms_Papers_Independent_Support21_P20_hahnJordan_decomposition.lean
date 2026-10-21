-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_hahnJordan_decomposition
-- name    : QAlgorithms.Papers.Independent.Support21.P20.hahnJordan_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:57:28.694075+00:00
-- url     : https://prove2.me/theorems/ec495b98-957a-4c5d-8ee7-fa72f125f42e
-- title:
--   Full Hahn–Jordan decomposition of normal valuations
-- statement:
--   Let $L$ be a Stonean locale and $\nu:L\to\mathbb R$ a finite normal valuation. The same assertions hold when $L$ is Boolean and $\nu$ is continuous. Define
--
--   $$p=\bigvee\{a:\forall b\le a,\ \nu(b)\ge0\},\qquad q=\bigvee\{a:\forall b\le a,\ -\nu(b)\ge0\}.$$
--
--   For every $a$, nonnegativity of $\nu$ on $[0,a]$ is equivalent to $a\le p$, and nonnegativity of $-\nu$ there is equivalent to $a\le q$. Consequently both suprema are maxima. Moreover $p\vee q=1$, and $p\wedge q$ is the largest $a$ on whose entire principal interval $\nu$ vanishes. The functions
--
--   $$\nu^+(x)=\nu(p\wedge x),\qquad \nu^-(x)=-\nu(q\wedge x)$$
--
--   are nonnegative normal valuations and satisfy $\nu=\nu^+-\nu^-$. Define $|\nu|=\nu^++\nu^-$ and $\|\nu\|=|\nu|(1)$. The carriers need not be disjoint. For a complex valuation in either regime, apply this construction to its real and imaginary parts to obtain the canonical four nonnegative normal summands, with coefficients $1,-1,i,-i$.
--
--   This gives the source's real and complex decompositions. **Formalization Note** The nonnegative real-valued parts are represented as real functions together with pointwise nonnegativity, rather than by clamping a possibly negative value.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 18, Lemma 2.59

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 2.59, PDF pp.18–19: both regimes and all real/complex decomposition clauses. -/
theorem hahnJordan_decomposition (L : Type u) [Order.Frame L] :
    (∀ nu : L → ℝ, IsJordanRegime nu → HahnJordanConclusions nu) ∧
    (∀ nu : L → ℂ, IsJordanRegime nu → ComplexJordanConclusions nu) := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
