-- Prove2me | Theorems.Thm_SYZ_hessian_moduli_metric_is_kahler
-- name    : SYZ.hessian_moduli_metric_is_kahler
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T04:14:19.224201+00:00
-- url     : https://prove2.me/theorems/2170425a-a187-42b2-94c6-7e960f4a6c7a
-- title:
--   SYZ Section 3: $\partial_a g_{bc} = \partial_b g_{ac}$ implies $d\,\omega_{\mathcal M}=0$
-- statement:
--   **From Eq. (3.4) to the Kähler property, Section 3 of Strominger–Yau–Zaslow.** Let $g_{ab}$ be a smooth family of $m\times m$ real matrices on the moduli parameters $t \in \mathbb R^m$ whose first derivatives are totally symmetric,
--   $$\partial_a g_{bc} = \partial_b g_{ac},$$
--   that is, a **Hessian** (affine-Kähler) metric. Form the moduli space $\mathcal M = \mathbb R^m\times\mathbb R^m$ with coordinates $(t^a, s^a)$, the block-diagonal metric
--   $$G \;=\; g_{ab}\,(dt^a dt^b + ds^a ds^b),$$
--   the constant almost complex structure $\mathcal J(\partial_{t^a}) = \partial_{s^a}$, $\mathcal J(\partial_{s^a}) = -\partial_{t^a}$, and the associated fundamental $2$-form $\omega_{\mathcal M}(X,Y) = G(\mathcal JX,Y) = g_{ab}\,dt^a\wedge ds^b$. Then
--   $$d\,\omega_{\mathcal M} \;=\; 0 .$$
--
--   Since $\mathcal J$ is constant in these coordinates its Nijenhuis tensor vanishes identically, so $\mathcal J$ is integrable and $(\mathcal M, G, \mathcal J)$ is Kähler. This is the step the paper makes immediately after deriving Eq. (3.4), and it is independent of the special Lagrangian geometry: it is a statement about Hessian metrics and their standard Kähler extensions.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, pp. 251 and 253-254, the metric and almost complex structure on the moduli space and the consequence of Eq. (3.4)

import Definitions.Def_syz_flat_model

namespace SYZ

theorem hessian_moduli_metric_is_kahler {m : ℕ}
    (g : Dom m → Matrix (Fin m) (Fin m) ℝ)
    (hsmooth : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun t => g t a b))
    (hsym : ∀ (a b c : Fin m) (t : Dom m),
      D (fun s => g s b c) a t = D (fun s => g s a c) b t) :
    IsClosed2Form (moduliKahler g) := by sorry

end SYZ
