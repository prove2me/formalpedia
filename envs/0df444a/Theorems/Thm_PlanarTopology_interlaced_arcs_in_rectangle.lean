-- Prove2me | Theorems.Thm_PlanarTopology_interlaced_arcs_in_rectangle
-- name    : PlanarTopology.interlaced_arcs_in_rectangle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T01:20:00.286642+00:00
-- url     : https://prove2.me/theorems/c6b27014-d5f6-49fc-95a6-4e13954c3e65
-- title:
--   Arcs with interlaced endpoints in a rectangle intersect
-- statement:
--   Two arcs in a rectangle whose endpoints interlace on the boundary must intersect. This is the form of the crossing principle used in Birkhoff's shooting argument.
--
--   Let $R=[a,b]\times[0,h]$ with $a<b$ and $h>0$. Let $\Gamma,\Gamma':[-1,1]\to R$ be continuous, and let $a\le\alpha<\gamma<\beta\le b$. Assume:
--
--   1. $\Gamma$ joins the bottom points $(\alpha,0)$ and $(\beta,0)$: $\Gamma(-1)=(\alpha,0)$ and $\Gamma(1)=(\beta,0)$;
--   2. $\Gamma'$ starts at the bottom point $(\gamma,0)$ lying strictly between them: $\Gamma'(-1)=(\gamma,0)$;
--   3. $\Gamma'$ ends outside the bottom segment spanned by $\Gamma$. That is, $\Gamma'(1)$ lies on one of the vertical sides $\{a\}\times[0,h]$ or $\{b\}\times[0,h]$, or on the bottom edge to the left of $\alpha$ or to the right of $\beta$.
--
--   Then there are $s,t\in[-1,1]$ with
--   $$
--   \Gamma(s)=\Gamma'(t).
--   $$
--
--   In Birkhoff's existence proof for retrograde orbits, $\Gamma$ and $\Gamma'$ are the curves in the (velocity angle, height) rectangle traced by the forward and backward shooting families. Their intersection produces the symmetric half-orbit. The curves need not be injective.
--
--   **Formalization Note** The plane is $\mathbb R\times\mathbb R$. Continuity and the containment in $R$ are only required on $[-1,1]$.
-- source:
--   G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Section 18 (the curves Gamma and Gamma' in the tau,y-rectangle 'necessarily intersect', fig. 5), reprinted in Collected Mathematical Papers Vol. 1, pp. 738-741; via R. Maehara, Amer. Math. Monthly 91 (1984) 641-643.

import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas

namespace PlanarTopology

theorem interlaced_arcs_in_rectangle (Γ Γ' : ℝ → ℝ × ℝ) (a b h α β γ : ℝ)
    (hab : a < b) (hh : 0 < h) (hαβ : α < β) (haα : a ≤ α) (hβb : β ≤ b)
    (hγ1 : α < γ) (hγ2 : γ < β)
    (hΓ : ContinuousOn Γ (Set.Icc (-1) 1)) (hΓ' : ContinuousOn Γ' (Set.Icc (-1) 1))
    (hΓR : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      a ≤ (Γ s).1 ∧ (Γ s).1 ≤ b ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ h)
    (hΓ'R : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      a ≤ (Γ' t).1 ∧ (Γ' t).1 ≤ b ∧ 0 ≤ (Γ' t).2 ∧ (Γ' t).2 ≤ h)
    (hΓ0 : Γ (-1) = (α, 0)) (hΓ1 : Γ 1 = (β, 0)) (hΓ'0 : Γ' (-1) = (γ, 0))
    (hend : (Γ' 1).1 = a ∨ (Γ' 1).1 = b ∨
      ((Γ' 1).2 = 0 ∧ ((Γ' 1).1 < α ∨ β < (Γ' 1).1))) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1, Γ s = Γ' t := by sorry

end PlanarTopology
