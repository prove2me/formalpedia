-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_pullback_snd_schemeHomOverEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/bdf5aaa5-7e4c-5bdb-b6a1-9feb89d74a90
-- title:
--   Base change of a relative group law along R → K
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $K$ be a commutative ring which is an $R$-algebra; write $t_K \colon \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by $\operatorname{algebraMap} R\,K$, and $f_K :=$ `pullback.snd` $\colon A \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$. Here, for $g \colon Y \to B$ and $f \colon X \to B$, `SchemeHomOver g f` denotes the type of pairs consisting of a morphism $\varphi \colon Y \to X$ together with a proof that $\varphi$ followed by $f$ equals $g$, and a `RelativeGroupLaw R f` is a structure assigning to every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inverse on `SchemeHomOver t f`, subject to associativity, both unit laws, the left inverse law, and compatibility of the operations with precomposition by morphisms of test schemes over $\operatorname{Spec} R$. The assertion is that there is a bijection $\sigma$ from `SchemeHomOver` $t_K\, f$ onto `SchemeHomOver` $(\mathbf{1}_{\operatorname{Spec} K})\, f_K$ such that for every relative group law $G$ on $f$ over $R$ there exists a relative group law $G'$ on $f_K$ over $K$ with $\sigma(G.\mathrm{mul}\,t_K\,P\,Q) = G'.\mathrm{mul}\,\mathbf{1}\,(\sigma P)\,(\sigma Q)$ for all $P, Q$, and $\sigma(G.\mathrm{one}\,t_K) = G'.\mathrm{one}\,\mathbf{1}$. Note that the single bijection $\sigma$ is produced before, and independently of, $G$, and that the compatibility is asserted only for the multiplication and the unit, and only at the test morphism $\mathbf{1}_{\operatorname{Spec} K}$.
--
--   This is the functor-of-points form of the statement that a relative group law base-changes along $R \to K$, recorded together with the identification of $\operatorname{Spec} K$-points of $A$ over $R$ with $\operatorname{Spec} K$-points of $A_K$ over $K$. It is used to transport group laws on a Weierstrass model to the fibre over $K$ before applying rigidity results at the level of $\operatorname{Spec} K$-points, as in [`WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isAlgClosed) and [`WeierstrassProjModel.RelativeGroupLaw.mul_comm_at_field_of_isElliptic_of_baseChangeIso`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_comm_at_field_of_isElliptic_of_baseChangeIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_pullback_snd_schemeHomOverEquiv.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.exists_pullback_snd_schemeHomOverEquiv
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (K : Type u) [CommRing K] [Algebra R K] :
    ∃ σ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f ≃
          SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∀ (G : WeierstrassProjModel.RelativeGroupLaw R f),
        ∃ G' : WeierstrassProjModel.RelativeGroupLaw K
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
          (∀ P Q, σ (G.mul (Spec.map (CommRingCat.ofHom (algebraMap R K))) P Q)
            = G'.mul (𝟙 _) (σ P) (σ Q))
          ∧ σ (G.one (Spec.map (CommRingCat.ofHom (algebraMap R K)))) = G'.one (𝟙 _) := by sorry
