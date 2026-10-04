-- Prove2me | Theorems.Thm_PhilipponMultiplicity_normalized_group_neighborhood_zariski_interior
-- name    : PhilipponMultiplicity.normalized_group_neighborhood_zariski_interior
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-03T09:32:03.294111+00:00
-- url     : https://prove2.me/theorems/05d37ae0-cbaa-4573-9337-209e9e3c296f
-- title:
--   Local Zariski density of normalized coordinate neighborhoods
-- statement:
--   Let $K$ be a Philippon base field, isometrically isomorphic to $\mathbb C$ or to a completed algebraic closure $\mathbb C_p$, and let $G$ be a finite product of embedded commutative algebraic groups. Let
--   $$A=\prod_i K^{n_i+1}$$
--   be the space of homogeneous coordinate tuples. Choose a pivot $c_i$ in each projective block and a representative $a\in A$ of the identity with
--   $$a_{i,c_i}=1,\qquad [a_i]=0_i.$$
--   For any neighborhood $V$ of $a$ in the norm topology of $A$, define
--   $$S_V=\{x\in G(K):\text{ some }v\in V\text{ satisfies }v_{i,c_i}=1\text{ and }[v_i]=x_i\text{ for all }i\}.$$
--   Then the Zariski closure of this set has nonempty interior in the actual embedded group:
--   $$\operatorname{Int}_{\mathrm{Zar}}\!\left(\overline{S_V}^{\mathrm{Zar}}\right)\ne\varnothing.$$
--
--   This local-density assertion relates norm-topology neighborhoods of normalized homogeneous coordinates to the group's induced Zariski topology. It applies to disconnected groups; the conclusion need not assert density in every component. The neighborhood need not itself be open, only contain an open neighborhood of $a$.
--
--   **Formalization Note.** The checked reduction proves normalization of nearby homogeneous lifts, regularity of the actual affine cone, homogeneous denominator extraction, and a finite basic-open neighborhood of the identity inside the Zariski closure. Its sole remaining input is the general [affine norm-germ comparison at a regular point](https://prove2.me/theorems/9c4e05d1-9433-4fdc-b067-407679064fff). The complete-field analytic/algebraic comparison, including the $\mathbb C_p$ case, remains Open. The original formal statement is unchanged.
-- source:
--   V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 3.1, Lemma 3.2 and its proof, printed p.114, https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . Their chapter assumes local compactness; the present auxiliary obligation includes the complete-field extension of the algebraic/analytic Taylor-series comparison used in that proof. For complete non-Archimedean fields see A. Chambert-Loir and F. Loeser, A non-archimedean Ax-Lindemann theorem, section 5.1, printed p.8, and the density of rational points used in the proof of Lemma 5.3, printed p.9, https://webusers.imj-prg.fr/~francois.loeser/drinfeldv3.pdf . The actual normalized-coordinate comparison, smooth identity-component restriction for disconnected groups, and passage to the stated Zariski interior are part of this Open specialization.

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false
open Filter Topology

namespace PhilipponMultiplicity

theorem normalized_group_neighborhood_zariski_interior
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K)
    (c : ∀ i : G.FactorIndex, Fin ((G.factor i).ambientDimension + 1))
    (a : G.ambient.Variable → K)
    (ha : ∀ i, a ⟨i, c i⟩ = 1)
    (harep : ∀ i, ∃ h : (fun j => a ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => a ⟨i, j⟩) h = G.embedding 0 i)
    (V : Set (G.ambient.Variable → K)) (hV : V ∈ 𝓝 a) :
    (@interior _ G.zariskiTopology
      (@closure _ G.zariskiTopology
        {x : G.Point | ∃ v ∈ V, (∀ i, v ⟨i, c i⟩ = 1) ∧
          ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i, j⟩) h = G.embedding x i})).Nonempty := by sorry

end PhilipponMultiplicity
