-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_group_geometry
-- name    : WeierstrassEllipticZeta.elliptic_extension_group_geometry
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-08T16:16:42.929586+00:00
-- url     : https://prove2.me/theorems/0ed62efa-96ec-408c-a239-d6a2f9c83686
-- title:
--   Canonical elliptic-extension quotient geometry and subgroup pullback
-- statement:
--   Let $L$ be a complex period pair with lattice $\Lambda$ and canonical Weierstrass zeta quasiperiods. There exists a $\mathbb Z$-linear map $\eta:\Lambda\to\mathbb C$ whose value at every period is its canonical zeta quasiperiod. Form
--
--   $$\Gamma_\eta=\{(\omega,-\eta(\omega)):\omega\in\Lambda\},\qquad
--   E_\eta=\mathbb C^2/\Gamma_\eta,\qquad G_\eta=\mathbb C\times E_\eta.$$
--
--   Define $i(u)=[(0,u)]$, $p([(z,u)])=z\bmod\Lambda$, and
--
--   $$\varphi(z)=(z,[(z,0)]),\quad p_a(t,e)=t,\quad p_E(t,e)=p(e).$$
--
--   The map $i$ is injective, $p$ is surjective, and $\ker p=\operatorname{im}i$. Also $p_a\circ\varphi=\mathrm{id}_{\mathbb C}$ and $p_E\circ\varphi=q_\Lambda$, where $q_\Lambda$ is the lattice quotient map.
--
--   For every additive subgroup $H\subseteq G_\eta$, put $K=\varphi^{-1}(H)$. If $H\subseteq\ker p_a$, then $K=\{0\}$. If $H\subseteq\ker p_E$, then $K\subseteq\Lambda$. For every finite $X\subset\mathbb C$, the quotient counts agree exactly:
--
--   $$|q_K(X)|=|q_H(\varphi(X))|.$$
--
--   Thus the additive extension sequence is exact, and subgroup profiles and finite quotient counts can be pulled back along the concrete one-parameter map. No finiteness assumption is made on $H$ or $K$. This statement concerns the additive quotient and its maps; it does not assert an algebraic-group structure, an algebraic subgroup classification, or a multiplicity theorem.
-- source:
--   Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, equation (A.3), the displayed exponential map and one-parameter curve before (A.4), and the quotient counts in Theorems A.2-A.3, https://doi.org/10.1017/S001309152610145X. This derived additive quotient model uses the exponential period pairs (omega,-eta(omega)). Canonical quasiperiod additivity is proved from the already-proved zeta translation identity. Exactness, projection pullbacks and finite quotient-count equality are proved directly; no algebraic-group or multiplicity assertion is included.

import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Data.Set.Card

open TranscendenceTheory WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.elliptic_extension_group_geometry (L : PeriodPair) :
    ∃ η : L.lattice →ₗ[ℤ] ℂ,
      (∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) ∧
      Function.Injective (extensionInclusion L.lattice η) ∧
      Function.Surjective (extensionProjection L.lattice η) ∧
      LinearMap.ker (extensionProjection L.lattice η) =
        LinearMap.range (extensionInclusion L.lattice η) ∧
      (extensionAdditiveProjection L.lattice η).comp (extensionCurve L.lattice η) =
        LinearMap.id ∧
      (extensionEllipticProjection L.lattice η).comp (extensionCurve L.lattice η) =
        L.lattice.mkQ ∧
      ∀ H : Submodule ℤ (GraphExtensionGroup L.lattice η),
        (H ≤ LinearMap.ker (extensionAdditiveProjection L.lattice η) →
          H.comap (extensionCurve L.lattice η) = ⊥) ∧
        (H ≤ LinearMap.ker (extensionEllipticProjection L.lattice η) →
          H.comap (extensionCurve L.lattice η) ≤ L.lattice) ∧
        ∀ X : Finset ℂ,
          ((H.comap (extensionCurve L.lattice η)).mkQ '' (X : Set ℂ)).ncard =
            (H.mkQ '' (extensionCurve L.lattice η '' (X : Set ℂ))).ncard := by sorry
