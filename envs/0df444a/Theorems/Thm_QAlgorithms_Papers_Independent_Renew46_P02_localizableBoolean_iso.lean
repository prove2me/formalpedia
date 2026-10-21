-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_localizableBoolean_iso
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.localizableBoolean_iso
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:50:30.537395+00:00
-- url     : https://prove2.me/theorems/b74b4a96-adfd-4588-b4a8-bbc2a91472f2
-- title:
--   Proposition 7.12: Localizability is invariant under measure-algebra isomorphism
-- statement:
--   Let $(B,\mu)$ and $(C,\nu)$ be measure algebras: sigma-complete Boolean algebras with strictly positive, countably additive $[0,\infty]$-valued measures. Let $e:B\to C$ be a Boolean isomorphism satisfying $\nu(e(b))=\mu(b)$ for every $b\in B$. Then
--
--   $$
--   (B,\mu)\text{ is localizable}\iff(C,\nu)\text{ is localizable}.
--   $$
--
--   Localizable means that every subset has a least upper bound and every nonzero element dominates a nonzero element of finite measure. A Boolean order isomorphism is used equivalently to a unital Boolean isomorphism.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 33, Proposition 7.12

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Proposition 7.12, PDF p.33. Boolean order isomorphisms preserve
finite Boolean operations, complements, bottom and top. -/
theorem localizableBoolean_iso {B : Type u} {C : Type v}
    [BooleanAlgebra B] [BooleanAlgebra C] (mu : BooleanMeasure B) (nu : BooleanMeasure C)
    (e : B ≃o C) (hmeas : ∀ a : B, nu.value (e a) = mu.value a) :
    IsLocalizableBoolean mu ↔ IsLocalizableBoolean nu := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
