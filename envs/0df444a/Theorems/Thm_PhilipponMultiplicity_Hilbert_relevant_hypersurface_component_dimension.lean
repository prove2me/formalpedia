-- Prove2me | Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_hypersurface_component_dimension
-- name    : PhilipponMultiplicity.Hilbert.relevant_hypersurface_component_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T00:57:17.286405+00:00
-- url     : https://prove2.me/theorems/35ee5924-2e0a-4588-a850-fe471435ed54
-- title:
--   Relevant components of a homogeneous prime hypersurface have dimension one less
-- statement:
--   Let $p$ be a multihomogeneous prime in a multiprojective coordinate ring over any field. Let $P\notin p$ be multihomogeneous of natural multidegree $D$. For every relevant minimal prime $q$ of $p+(P)$,
--   $$\dim_H(q)+1=\dim_H(p),$$
--   where $\dim_H$ is the degree of the actual multigraded Hilbert polynomial. Zero entries of $D$ are permitted. If there is no relevant cut component, the assertion is vacuous. There is no component-dimension hypothesis in this statement: establishing this equality is the theorem itself.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, proof of Proposition 3.3, printed p. 368, the hypersurface component/dimension-slice step; https://www.numdam.org/articles/10.24033/bsmf.2060/ . The reduction uses the explicitly tracked affine altitude formula and the existing relevant-cone Hilbert–Krull comparison.

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem PhilipponMultiplicity.Hilbert.relevant_hypersurface_component_dimension
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(p : Ideal M.CoordinateRing)
    (hp : p.IsPrime) (hpH : IsMultihomogeneousIdeal M p)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPp : P ∉ p)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes)
    (hqr : IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q + 1 = idealDimension M p := by sorry
