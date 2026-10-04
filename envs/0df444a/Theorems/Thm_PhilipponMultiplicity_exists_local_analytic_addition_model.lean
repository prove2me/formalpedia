-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_local_analytic_addition_model
-- name    : PhilipponMultiplicity.exists_local_analytic_addition_model
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-02T22:04:26.19134+00:00
-- url     : https://prove2.me/theorems/1c4c4b85-a17a-49d8-91cc-7e289621e4ed
-- title:
--   Local analytic addition coordinates with Zariski-thick neighborhoods
-- statement:
--   Let $K$ be a Philippon base field, namely a normed field isometrically isomorphic to $\mathbb C$ or to a completed algebraic closure $\mathbb C_p$. Let $G$ be a finite product of embedded commutative algebraic groups over $K$, with its induced Zariski topology. There exist a nonnegative integer $d$ and maps
--   $$\phi:K^d\longrightarrow G(K),\qquad \mu:K^d\times K^d\longrightarrow K^d$$
--   with the following properties.
--
--   1. The origins correspond to the identity, and the local addition law is analytic at the origin:
--   $$\phi(0)=0,\qquad \mu(0,0)=0,\qquad \mu\text{ is }K\text{-analytic at }(0,0).$$
--   2. On sufficiently small neighborhoods of zero in the norm topology, the two unit identities and compatibility with the group law hold:
--   $$\mu(u,0)=u,\qquad \mu(0,v)=v,\qquad \phi(\mu(u,v))=\phi(u)+\phi(v).$$
--   Each identity is asserted as a germ at the corresponding origin; a common global neighborhood is not prescribed.
--   3. For every norm-topology neighborhood $U$ of zero in $K^d$, the image has a Zariski closure with nonempty interior in $G(K)$:
--   $$\operatorname{Int}_{\mathrm{Zar}}\!\left(\overline{\phi(U)}^{\mathrm{Zar}}\right)\ne\varnothing.$$
--
--   This local model connects analytic calculations at the identity with the Zariski topology of the given algebraic group. It contains no integer-multiplication map, and it does not assume connectedness. The parameter dimension may be zero.
--
--   **Formalization Note.** Analyticity and the identities are neighborhood germs. The maps need not be globally injective or globally compatible with addition. This is an auxiliary consequence of smooth algebraic-group coordinates and local Zariski density, specialized to the given embedded groups. The normalized chart required by the current reduction is recorded separately in [normalized analytic coordinates at the identity](https://prove2.me/theorems/79454bba-6628-4044-91b5-de684812a342); its existence remains Open.
-- source:
--   T. Q. Pham, Weil's Conjecture on Tamagawa Number, section 5.3, Proposition 84, printed p.32, https://toanqpham.github.io/Tamagawa.pdf (functorial analytic coordinates over a complete valued field). V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 3.1, Proposition 3.1, pp.110-112, and Lemma 3.2 with its Taylor-series proof, p.114, https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . Their chapter assumes local compactness; this auxiliary statement uses the same local coordinate and Taylor-series argument over C_p, without claiming C_p is locally compact. For the non-Archimedean density input over complete fields, see A. Chambert-Loir and F. Loeser, A non-archimedean Ax-Lindemann theorem, section 5.1, p.8, https://webusers.imj-prg.fr/~francois.loeser/drinfeldv3.pdf (proper algebraic closed subsets have analytifications with empty interior). The smooth-group comparison, actual embedded-group topology, local law and density are all part of this Open auxiliary obligation.

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false
open Filter Topology

namespace PhilipponMultiplicity

theorem exists_local_analytic_addition_model
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) :
    ∃ (d : ℕ) (φ : (Fin d → K) → G.Point)
      (μ : ((Fin d → K) × (Fin d → K)) → (Fin d → K)),
      φ 0 = 0 ∧ AnalyticAt K μ 0 ∧ μ 0 = 0 ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (u, 0) = u) ∧
      (∀ᶠ u in 𝓝 (0 : Fin d → K), μ (0, u) = u) ∧
      (∀ᶠ z in 𝓝 (0 : (Fin d → K) × (Fin d → K)),
        φ (μ z) = φ z.1 + φ z.2) ∧
      (∀ U : Set (Fin d → K), U ∈ 𝓝 0 →
        (@interior _ G.zariskiTopology
          (@closure _ G.zariskiTopology (φ '' U))).Nonempty) := by sorry

end PhilipponMultiplicity
