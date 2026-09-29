-- Prove2me | Theorems.Thm_Schanuel_e_pi_algebraicIndependent_of_schanuel
-- name    : Schanuel.e_pi_algebraicIndependent_of_schanuel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T17:38:42.151122+00:00
-- url     : https://prove2.me/theorems/329cf71f-403e-4310-9a84-6d8490471f36
-- title:
--   Schanuel's conjecture implies the algebraic independence of $e$ and $\pi$
-- statement:
--   **Schanuel's conjecture implies that $e$ and $\pi$ are algebraically independent.** Assume Schanuel's conjecture: for every $n$ and all complex numbers $z_1,\dots,z_n$ linearly independent over $\mathbb{Q}$, the field $\mathbb{Q}(z_1,\dots,z_n,e^{z_1},\dots,e^{z_n})$ has transcendence degree at least $n$ over $\mathbb{Q}$. Then $e$ and $\pi$ are algebraically independent over $\mathbb{Q}$: no nonzero polynomial $P \in \mathbb{Q}[X, Y]$ satisfies $P(e, \pi) = 0$.
--
--   The classical derivation applies the conjecture to the pair $(1, i\pi)$, which is linearly independent over $\mathbb{Q}$ since $\pi$ is irrational; the resulting field $\mathbb{Q}(1, i\pi, e, e^{i\pi}) = \mathbb{Q}(i\pi, e)$ must then have transcendence degree at least $2$. In particular $e + \pi$, $e\pi$, $e - \pi$ and $e/\pi$ are all irrational, none of which is known unconditionally.
-- source:
--   S. Lang, Introduction to Transcendental Numbers, Addison-Wesley, 1966, Chapter III; https://en.wikipedia.org/wiki/Schanuel%27s_conjecture (section 'Consequences')

import Mathlib

namespace Schanuel
theorem e_pi_algebraicIndependent_of_schanuel
    (schanuel : ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
      (n : Cardinal) ≤ Algebra.trdeg ℚ
        (IntermediateField.adjoin ℚ (Set.range z ∪ Set.range (Complex.exp ∘ z)))) :
    AlgebraicIndependent ℚ ![Complex.exp 1, (Real.pi : ℂ)] := by sorry
end Schanuel
