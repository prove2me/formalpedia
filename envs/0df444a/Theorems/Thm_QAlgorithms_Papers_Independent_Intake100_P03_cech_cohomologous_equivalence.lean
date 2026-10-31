-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P03_cech_cohomologous_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P03.cech_cohomologous_equivalence
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-30T12:42:08.465857+00:00
-- url     : https://prove2.me/theorems/cb4f6939-ad28-45ed-b751-e4a2161fccc4
-- title:
--   Continuous Čech cocycles on a fixed cover: cohomologousness is an equivalence relation
-- statement:
--   Let $M$ be a compactly generated weak Hausdorff space, let $\mathcal U=(U_i)_{i\in I}$ be any open cover of $M$, and let $\mathcal C=(G,H,t,\alpha)$ be a topological crossed module in compactly generated weak Hausdorff spaces. Thus $t:H\to G$ is continuous, $\alpha$ is a jointly continuous action on the k-product by automorphisms, and equivariance and the Peiffer identity hold. Write $Z^1(\mathcal U,\mathcal C)$ for the normalized continuous cocycles: their transition maps $g_{ij}:U_i\cap U_j\to G$ and $h_{ijk}:U_i\cap U_j\cap U_k\to H$ satisfy the triangle and tetrahedron diagrams, with $g_{ii}=1$ and $h_{ijk}=1$ whenever two indices agree.
--
--   For $z=(g,h)$ and $z'=(g',h')$ in this set, define $z\sim z'$ to mean that there are continuous maps $f_i:U_i\to G$ and $k_{ij}:U_i\cap U_j\to H$, with $k_{ii}=1$, satisfying, on the relevant overlaps,
--   $$
--   t(k_{ij})g_{ij}f_j=f_i g'_{ij},\qquad
--   k_{ik}h_{ijk}=\alpha(f_i)(h'_{ijk})\,k_{ij}\,\alpha(g_{ij})(k_{jk}).
--   $$
--   These are the naturality square and the prism coherence, respectively. Then this raw relation is an equivalence relation:
--   $$
--   \begin{gathered}
--   \forall z,\ z\sim z,\\
--   \forall z,z',\ z\sim z'\Longrightarrow z'\sim z,\\
--   \forall z,z',z'',\ (z\sim z'\ \text{and}\ z'\sim z'')\Longrightarrow z\sim z''.
--   \end{gathered}
--   $$
--   This supplies the equivalence relation used to form the fixed-cover continuous nonabelian Čech set. No good-cover, paracompactness, well-pointedness, connectedness, or nonemptiness hypothesis is needed.
--
--   **Formalization Note** The cocycle tetrahedron is $h_{ikl}h_{ijk}=h_{ijl}\alpha(g_{ij})(h_{jkl})$, as forced by diagram (6) and the source's vertical composition rule. The scalar transcription (2) prints the factors in the reverse order. This correction was independently checked in moderation round 1; no equivalence closure is used in defining $\sim$.
-- source:
--   The Classifying Space of a Topological 2-Group, arXiv:0801.3843v2, PDF p. 15, Section 4, unnumbered equivalence-relation assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P03

namespace QAlgorithms.Papers.Independent.Intake100.P03

universe u

/-- Section 4, PDF p. 15 (with the definitions on pp. 13--15): raw
cohomologousness of continuous normalized Cech cocycles on any fixed
open cover is an equivalence relation. No good-cover, paracompactness,
well-pointedness, connectedness or nonemptiness condition is imposed.
Source correction E2 (PDF pp. 5,14):
Printed: alpha(g_ij)(h_jkl) * h_ijl = h_ijk * h_ikl.
Changed: h_ikl * h_ijk = h_ijl * alpha(g_ij)(h_jkl).
Why: diagram (6), target t(h)g, and vertical composition hprime*h
on pp. 9,12 force precisely the changed product order. All triangle,
normalization, continuity and transformation laws are retained.
The independent round-1 moderator checked this correction against the
PDF diagrams and a noncommutative instance; see MODERATION-r1.md. -/
theorem cech_cohomologous_equivalence {M I G H : Type u}
    [TopologicalSpace M] [TopologicalSpace G] [TopologicalSpace H]
    [Group G] [Group H] (hM : IsKSpace M)
    (C : TopologicalCrossedModule G H) (U : OpenCover M I) :
    Equivalence (Cohomologous (C := C) (U := U)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P03
