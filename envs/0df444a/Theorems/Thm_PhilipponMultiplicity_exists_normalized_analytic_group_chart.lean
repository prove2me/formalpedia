-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_normalized_analytic_group_chart
-- name    : PhilipponMultiplicity.exists_normalized_analytic_group_chart
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-03T08:25:37.247273+00:00
-- url     : https://prove2.me/theorems/79454bba-6628-4044-91b5-de684812a342
-- title:
--   Normalized analytic coordinates at the group identity
-- statement:
--   Let $K$ be a Philippon base field, isometrically isomorphic to $\mathbb C$ or to a completed algebraic closure $\mathbb C_p$. Let $G$ be a finite product of embedded commutative algebraic groups over $K$. Write $I$ for its finite set of projective blocks, $n_i$ for the ambient dimension of block $i$, and
--   $$A=\prod_{i\in I}K^{n_i+1}$$
--   for the space of homogeneous coordinate tuples.
--
--   There exist a nonnegative integer $d$, a pivot index $c_i$ in each block, maps
--   $$\phi:K^d\longrightarrow G(K),\qquad f:K^d\longrightarrow A,$$
--   and a continuous $K$-linear map
--   $$\rho:A\longrightarrow K^d$$
--   with the following properties.
--
--   1. The parameter origin represents the identity, and the coordinate lift is analytic there:
--
--      $$\phi(0)=0,\qquad f\text{ is analytic at }0.$$
--
--   2. For every parameter $u$, the coordinates are normalized and represent the actual embedded group point:
--
--      $$f(u)_{i,c_i}=1,\qquad [f(u)_i]=\phi(u)_i\quad(i\in I).$$
--
--   3. The linear projection of the centered coordinates is a local inverse on the parameter side:
--
--      $$\rho(f(u)-f(0))=u$$
--
--      for all sufficiently small $u$.
--
--   4. There is also a neighborhood $V$ of $f(0)$ in the norm topology of $A$ with this inverse property: whenever $v\in V$ is normalized at the chosen pivots and its projective blocks represent a point $x\in G(K)$, one has
--
--      $$\phi\bigl(\rho(v-f(0))\bigr)=x.$$
--
--   5. Every parameter neighborhood $U$ of zero has an image whose Zariski closure has nonempty interior in the given group:
--
--      $$\operatorname{Int}_{\mathrm{Zar}}\!\left(\overline{\phi(U)}^{\mathrm{Zar}}\right)\ne\varnothing.$$
--
--   This is a smooth local chart at the identity, expressed entirely through normalized ambient coordinates. Neither a coordinate formula for addition nor compatibility with a local addition law is included in its conclusions. No connectedness or positive dimension is assumed.
--
--   **Formalization Note.** Total functions encode a local chart whose inverse identities are neighborhood germs. This auxiliary statement specializes smooth-variety coordinates and local Zariski density to the given embedded-group presentation. Its remaining geometric inputs are recorded separately as [a nonsingular normalized polynomial presentation](https://prove2.me/theorems/26ef4e3a-97d2-4ca0-bbfe-7f1f05265761) and [local density of normalized coordinate neighborhoods](https://prove2.me/theorems/05d37ae0-cbaa-4573-9337-209e9e3c296f); both remain Open.
-- source:
--   V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 3.1, Theorem 3.2 and the coordinate-projection construction, pp.110-111, Proposition 3.1, pp.111-112, and Lemma 3.2, p.114, https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . That chapter assumes local compactness. The present auxiliary statement adapts the smooth-coordinate and Taylor-series arguments to complete valued fields, including C_p; it does not assume C_p is locally compact. For that field scope see T. Q. Pham, Weil's Conjecture on Tamagawa Number, section 5.3, Proposition 84, printed p.32, https://toanqpham.github.io/Tamagawa.pdf (smooth finite-type schemes over a complete valued field, with etale maps inducing local analytic isomorphisms). For non-Archimedean local density see A. Chambert-Loir and F. Loeser, A non-archimedean Ax-Lindemann theorem, section 5.1, printed p.8, https://webusers.imj-prg.fr/~francois.loeser/drinfeldv3.pdf (empty interior of analytifications of proper closed subvarieties of an irreducible variety). Smoothness at the group identity, the comparison with the actual normalized embedded coordinates, and local Zariski density are explicit parts of this Open auxiliary obligation.

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false
open Filter Topology

namespace PhilipponMultiplicity

theorem exists_normalized_analytic_group_chart
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (f : (Fin d → K) → G.ambient.Variable → K)
      (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
      (ρ : (G.ambient.Variable → K) →L[K] (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K f 0 ∧
      (∀ u i, f u ⟨i, c i⟩ = 1) ∧
      (∀ u i, ∃ h : (fun j => f u ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f u ⟨i, j⟩) h = G.embedding (φ u) i) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), ρ (f u - f 0) = u) ∧
      (∀ᶠ v in 𝓝 (f 0), (∀ i, v ⟨i, c i⟩ = 1) →
        ∀ x : G.Point,
          (∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i) →
          φ (ρ (v - f 0)) = x) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty) := by sorry

end PhilipponMultiplicity
