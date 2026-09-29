-- Prove2me | Theorems.Thm_PowerSeries_existsUnique_ringHom_of_isAdicComplete
-- name    : PowerSeries.existsUnique_ringHom_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/3dc863b2-0706-58b2-ac76-06a0b12b51d6
-- title:
--   Evaluation of power series in an adically complete ring
-- statement:
--   Let $A$ and $S$ be commutative rings, let $J$ be an ideal of $S$ such that $S$ is $J$-adically complete in Mathlib's sense (the $J$-adic filtration is separated and every Cauchy-type compatible family of approximate solutions is realised by an element of $S$), let $\theta : A \to S$ be a ring homomorphism, and let $x$ be an element of $J$. The assertion is that there exists a unique ring homomorphism $\varphi : A[\![X]\!] \to S$ with the property that for every formal power series $F$ over $A$ and every natural number $n$, the difference $$\varphi(F) - \sum_{i<n} \theta(a_i)\, x^{i} \in J^{n},$$ where $a_i$ is the $i$-th coefficient of $F$; that is, $\varphi(F)$ is congruent modulo $J^n$ to the image under $\theta$ of the truncation of $F$ at order $n$, evaluated at $x$. Uniqueness is uniqueness among ring homomorphisms satisfying all these congruences simultaneously. Taking $F$ constant gives $\varphi \circ (\text{constant coefficient}) = \theta$ and taking $F = X$ gives $\varphi(X) = x$, but the statement is phrased by the congruences rather than by these two conditions.
--
--   This is the universal property of the formal power series ring with respect to adically complete target rings: substitution of a topologically nilpotent element, here an element of the defining ideal, for the variable. It provides a purely algebraic evaluation map, without any topology on $S$, and is used to construct homomorphisms from one-variable power series rings over a coefficient ring into adic completions of local rings arising from integral models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_existsUnique_ringHom_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.existsUnique_ringHom_of_isAdicComplete {A S : Type*} [CommRing A] [CommRing S]
    (J : Ideal S) [IsAdicComplete J S] (θ : A →+* S) (x : S) (hx : x ∈ J) :
    ∃! φ : PowerSeries A →+* S,
      ∀ (F : PowerSeries A) (n : ℕ),
        φ F - (Finset.range n).sum (fun i => θ (PowerSeries.coeff i F) * x ^ i) ∈ J ^ n := by sorry
