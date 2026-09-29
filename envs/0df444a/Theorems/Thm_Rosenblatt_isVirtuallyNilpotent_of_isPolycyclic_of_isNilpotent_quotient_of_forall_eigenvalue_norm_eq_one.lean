-- Prove2me | Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one
-- name    : Rosenblatt.isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-21T18:32:15.223334+00:00
-- url     : https://prove2.me/theorems/3e0ca4e1-f18c-416d-bfc2-dc15d3814966
-- title:
--   Theorem 4.12, linear-algebra half: if every eigenvalue of every conjugation lies on the unit circle then the group is almost nilpotent
-- statement:
--   Let $\Gamma$ be a polycyclic group with a **normal** subgroup $A$ carrying an
--   isomorphism $A \cong \mathbb{Z}^k$, such that $\Gamma/A$ is **nilpotent**. Suppose given, for
--   each $g \in \Gamma$, an integer $k \times k$ matrix $T_g$ representing conjugation by $g$ in
--   those coordinates:
--   $$g \cdot \iota(z) \cdot g^{-1} = \iota(T_g z) \qquad\text{for all } z \in \mathbb{Z}^k,$$
--   where $\iota$ is the isomorphism $\mathbb{Z}^k \to A \le \Gamma$. If **every** complex
--   eigenvalue of **every** $T_g$ has modulus $1$, then $\Gamma$ is almost nilpotent.
--
--   *Reading the pieces.* $\mathbb{Z}^k$ appears as `Multiplicative (Fin k → ℤ)`, the additive group
--   written multiplicatively. Matrices act on column vectors from the left. The eigenvalue condition
--   is quantified over every group element, every complex number and every nonzero complex vector,
--   and the norm is that of a **scalar** — the modulus of the eigenvalue — not a matrix norm.
--   "Almost nilpotent" is Mathlib's `Group.IsVirtuallyNilpotent`: a nilpotent subgroup of finite
--   index, not required to be normal.
--
--   *What the conjugation hypothesis forces.* Because it is asserted for every $g$ and every $z$, it
--   pins conjugation in both directions and makes the family $g \mapsto T_g$ a group homomorphism
--   $\Gamma \to GL_k(\mathbb{Z})$: one gets $T_1 = I$, $T_{g^{-1}} = T_g^{-1}$ and
--   $\det T_g = \pm 1$ for free. None of that has to be assumed.
--
--   *Redundancy and degeneracy, stated because they are real.* The normality of $A$ is
--   mathematically redundant — it follows from the conjugation hypothesis — but it is retained
--   because the nilpotency hypothesis on $\Gamma/A$ cannot even be stated without it. The polycyclic
--   hypothesis is not needed either: the conclusion holds for any group with a normal subgroup
--   $A \cong \mathbb{Z}^k$ and nilpotent $\Gamma/A$ under the eigenvalue condition. It is retained
--   because Rosenblatt's Theorem 4.12, which this statement serves, is about polycyclic groups. The
--   only degenerate rank is $k = 0$, where there is no nonzero vector and $A$ is forced to be
--   trivial.
--
--   The hypotheses are satisfiable, and not only in abelian examples: the infinite dihedral group
--   with $A$ its subgroup of translations and $T_g = (\pm 1)$ satisfies all of them, with a
--   nilpotent quotient of order two.
-- source:
--   Rosenblatt, J. M., Invariant measures and growth conditions, Transactions of the American Mathematical Society 193 (1974) 33–53, https://doi.org/10.1090/S0002-9947-1974-0342955-9, Theorem 4.12, pp. 48-49, the part of the proof after Theorem 4.17 has been applied

import Definitions.Def_MilnorWolf_Growth
import Mathlib

namespace Rosenblatt

open scoped Matrix

theorem isVirtuallyNilpotent_of_isPolycyclic_of_isNilpotent_quotient_of_forall_eigenvalue_norm_eq_one
    {G : Type*} [Group G] {k : ℕ} (hpoly : MilnorWolf.IsPolycyclic G)
    (A : Subgroup G) [A.Normal] (e : A ≃* Multiplicative (Fin k → ℤ))
    (T : G → Matrix (Fin k) (Fin k) ℤ)
    (hT : ∀ (g : G) (z : Fin k → ℤ),
      g * ((e.symm (Multiplicative.ofAdd z) : A) : G) * g⁻¹
        = ((e.symm (Multiplicative.ofAdd (T g *ᵥ z)) : A) : G))
    (hnil : Group.IsNilpotent (G ⧸ A))
    (heig : ∀ (g : G) (φ : ℂ) (v : Fin k → ℂ), v ≠ 0 →
      ((T g).map (fun z : ℤ => (z : ℂ))) *ᵥ v = φ • v → ‖φ‖ = 1) :
    Group.IsVirtuallyNilpotent G := by
  sorry

end Rosenblatt
