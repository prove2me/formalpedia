-- Prove2me | Theorems.Thm_SP4Seam_seam_transition_compatibility
-- name    : SP4Seam.seam_transition_compatibility
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T07:01:25.463374+00:00
-- url     : https://prove2.me/theorems/f1e93fb9-c414-46aa-8b6c-fc6978243ee7
-- title:
--   Seam–interior smooth compatibility for the two-disk quotient
-- statement:
--   Let $m\in\mathbb N$, let $E_m=\mathbb R^{m+1}$, and put $D^{m+1}=\{w\in E_m:\|w\|\leq1\}$ and $S^m=\{u\in E_m:\|u\|=1\}$, with their Euclidean subspace topologies. Give $S^m$ its standard stereographic smooth structure. Fix a homeomorphism $\varphi:S^m\to S^m$. Let
--   $$
--   Q_\varphi=(D^{m+1}_L\sqcup D^{m+1}_R)/(u_L\sim\varphi(u)_R)
--   $$
--   have the quotient topology, where the displayed pairs generate the equivalence relation. Write $[w]_L,[w]_R$ for the quotient images, $V_L=\{[w]_L:\|w\|<1\}$, and $V_R=\{[w]_R:\|w\|<1\}$.
--
--   The open seam $U_\varphi$ is the image of the explicit bicollar
--   $$
--   c_\varphi:S^m\times(-1,1)\longrightarrow Q_\varphi,\qquad
--   c_\varphi(u,t)=
--   \begin{cases}
--   [(1-t/2)u]_L,&0\leq t<1,\\
--   [(1+t/2)\varphi(u)]_R,&-1<t<0.
--   \end{cases}
--   $$
--   This is the source's homeomorphism onto the open seam; $U_\varphi,V_L,V_R$ are open and cover the quotient. The two interiors are disjoint. The quotient seam itself corresponds to $t=0$.
--
--   For each $x\in U_\varphi$, write $c_\varphi^{-1}(x)=(u_x,t_x)$. Let $\sigma_{u_x}$ be the standard stereographic chart selected at $u_x$, including the source's orthonormal-basis identification with $\mathbb R^m$, and let $A_m:\mathbb R^m\times\mathbb R\to E_m$ be the continuous linear identification $A_m(a,t)=(t,a)$. The seam regional chart $\chi_x$ is specified by
--   $$
--   \chi_x(c_\varphi(u,t))=A_m(\sigma_{u_x}(u),t)
--   $$
--   on its chart source. For every $y_L\in V_L$ and $y_R\in V_R$, the corresponding regional charts $\lambda_{y_L}$ and $\rho_{y_R}$ give the original Euclidean disk-interior coordinates, $\lambda_{y_L}([w]_L)=w$ and $\rho_{y_R}([w]_R)=w$. These regional charts are partial homeomorphisms from the actual quotient to $E_m$, obtained using the open-region inclusions.
--
--   For any two such regional charts $a,b$, define $T_{a\to b}=b\circ a^{-1}$ only on its natural overlap domain $a(\operatorname{dom}a\cap\operatorname{dom}b)$. Every smoothness assertion below is $C^\infty$ over $\mathbb R$ on exactly that domain, including the case of an empty overlap. It does not assert smoothness of a totalized inverse outside the domain. All dimensions $m\geq0$ are included.
--
--   For every $m\in\mathbb N$ and every homeomorphism $\varphi:S^m\to S^m$, the explicit regional charts on $Q_\varphi$ satisfy all four assertions: (i) for every $x\in U_\varphi,y_L\in V_L$, the seam-to-left-interior transition is $C^\infty$ on its natural overlap source; (ii) for every such $x,y_L$, the reverse transition is $C^\infty$ on its natural overlap source; (iii) if $\varphi^{-1}$ is smooth between the standard spheres, then for every $x\in U_\varphi,y_R\in V_R$, the right-interior-to-seam transition is $C^\infty$ on its natural overlap source; and (iv) if $\varphi$ is smooth between the standard spheres, then for every such $x,y_R$, the seam-to-right-interior transition is $C^\infty$ on its natural overlap source. The smoothness assumptions in (iii) and (iv) remain inside their respective implications. In particular, a smooth boundary diffeomorphism supplies both assumptions, without changing the stronger unconditional left-side assertions.
--
--   For $u$ in the sphere chart source, the geometric overlap formulas, before application of $\sigma_{u_x}$ and $A_m$, are
--   $$
--   \begin{array}{ll}
--   U_\varphi\to V_L:&(u,t)\mapsto(1-t/2)u,\quad 0<t<1,\\
--   V_L\to U_\varphi:&w\mapsto(w/\|w\|,\,2(1-\|w\|)),\\
--   U_\varphi\to V_R:&(u,t)\mapsto(1+t/2)\varphi(u),\quad -1<t<0,\\
--   V_R\to U_\varphi:&w\mapsto(\varphi^{-1}(w/\|w\|),\,-2(1-\|w\|)).
--   \end{array}
--   $$
--   In both inverse formulas, $1/2<\|w\|<1$. The actual inverse overlap additionally requires $w/\|w\|$ on the left, or $\varphi^{-1}(w/\|w\|)$ on the right, to belong to the source of $\sigma_{u_x}$. Thus the domain must not be replaced by the whole annulus. These formulas identify the coordinate changes being asserted smooth; they are not a proof explanation.
--
--   This single target groups four proved assertions from the cited source. It concerns actual regional chart transitions; it does not assert a global smooth-manifold instance, a diffeomorphism with the standard sphere, or a decomposition of an arbitrary homotopy sphere into two standard disks.
-- source:
--   Ryan Shin, Hemisphere.lean, unpublished Lean source (2026): contDiffOn_seam_interiorFst_trans, lines 2439–2460; contDiffOn_seam_interiorFst_trans_symm, lines 2944–2974; contDiffOn_seam_interiorSnd_trans_symm, lines 3393–3423; contDiffOn_seam_interiorSnd_trans, lines 3555–3577. Original file SHA-256 c48843d2c4ec6987acfd7f7ab3a92bfed990376206142e74712795b4e9399828. The new public name groups these four source assertions as a conjunction, not a fifth independent geometric result. Original file was untracked; no commit blob is claimed.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts
import Definitions.Def_SP4SeamPullbackGroupoid
import Definitions.Def_SP4SeamDisk
import Definitions.Def_SP4SeamHemispherePart1
import Definitions.Def_SP4SeamHemispherePart2
import Definitions.Def_SP4SeamHemispherePart3

set_option autoImplicit false
open Set Metric SP4Gluing SPC4Disk SP4Seam
open scoped ContDiff Manifold

theorem SP4Seam.seam_transition_compatibility {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    (∀ (x : openSeam φ) (y : interiorFst φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorFst φ) y))
        ((regionChart (isOpen_openSeam φ) x).symm.trans
          (regionChart (isOpen_interiorFst φ) y)).source) ∧
    (∀ (x : openSeam φ) (y : interiorFst φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_interiorFst φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x))
        ((regionChart (isOpen_interiorFst φ) y).symm.trans
          (regionChart (isOpen_openSeam φ) x)).source) ∧
    (ContMDiff (𝓡 m) (𝓡 m) ∞ φ.symm →
      ∀ (x : openSeam φ) (y : interiorSnd φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_interiorSnd φ) y).symm.trans
        (regionChart (isOpen_openSeam φ) x))
        ((regionChart (isOpen_interiorSnd φ) y).symm.trans
          (regionChart (isOpen_openSeam φ) x)).source) ∧
    (ContMDiff (𝓡 m) (𝓡 m) ∞ φ →
      ∀ (x : openSeam φ) (y : interiorSnd φ),
      ContDiffOn ℝ ∞ ((regionChart (isOpen_openSeam φ) x).symm.trans
        (regionChart (isOpen_interiorSnd φ) y))
        ((regionChart (isOpen_openSeam φ) x).symm.trans
          (regionChart (isOpen_interiorSnd φ) y)).source) := by sorry
