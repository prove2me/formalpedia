-- Prove2me | Theorems.Thm_RiemannMasullo_adele_additive_quotient
-- name    : RiemannMasullo.adele_additive_quotient
-- status  : Proved
-- author  : @koffie
-- created : 2026-11-20T23:16:37.771958+00:00
-- url     : https://prove2.me/theorems/626d64f0-a84e-4c67-97d4-3fb0bc37c2f5
-- title:
--   Lemma A.1.2.1 — the additive adelic quotient $\mathbb A_F/F$ and functoriality of adeles
-- statement:
--   Let $F$ be a number field with adele ring $\mathbb A_F$, and let $d:F\to\mathbb A_F$ be the diagonal embedding with quotient map $q:\mathbb A_F\to\mathbb A_F/F$. Let $\mathbb A_F^{\mathrm{int}}\subseteq\mathbb A_F$ be the adeles integral at every finite place, and $q_0:\mathbb A_F^{\mathrm{int}}\to\mathbb A_F^{\mathrm{int}}/\mathcal O_F$ the quotient by the integral diagonal. Then:
--
--   1. $d$ is injective, and $d(F)$ is closed and discrete in $\mathbb A_F$.
--   2. The sequence $F\xrightarrow{d}\mathbb A_F\xrightarrow{q}\mathbb A_F/F$ is exact, and $q$ is an open quotient map.
--   3. $\mathbb A_F/F$ is compact Hausdorff, and multiplication by every positive integer $n$ is a bijection of $\mathbb A_F/F$.
--   4. Inclusion induces an isomorphism of topological groups $\mathbb A_F^{\mathrm{int}}/\mathcal O_F\cong\mathbb A_F/F$, compatible with $q_0$ and $q$.
--   5. For every embedding $\sigma:F\to L$ of number fields there is a unique continuous ring homomorphism $f:\mathbb A_F\to\mathbb A_L$ extending $\sigma$ on the diagonal and acting place by place. Every such $f$ restricts to the integral adeles and induces continuous maps $\mathbb A_F/F\to\mathbb A_L/L$ and $\mathbb A_F^{\mathrm{int}}/\mathcal O_F\to\mathbb A_L^{\mathrm{int}}/\mathcal O_L$ compatible with the quotient maps.
--
--   This is the additive part of the adelic foundations in Appendix A: compactness of $\mathbb A_F/F$ and functoriality of adeles under field embeddings.
--
--   **Formalization Note** "Acting place by place" is the predicate `IsAdeleExtension`: a component of $f(a)$ at a place $w$ of $L$ vanishes whenever the component of $a$ at the place below $w$ vanishes.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/9d5c8b94a1f1b5d8f903f1b04d1e043877e7bb15/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L763-L807 (R. McCorvie et al., riemann-masullo, Apache-2.0); A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Lemma A.1.2.1, pp. 540–541.

import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions
import Definitions.Def_RiemannMasullo_IntegralAdeleDiagonal

open Function NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "AQuot(" F ")" => 𝔸[F] ⧸ AdeleRing.principalSubgroup (𝓞 F) F
local notation "IQuot(" F ", " S ")" =>
  (RiemannMasullo.integralAdelesOutside F S) ⧸
    AddMonoidHom.range (RingHom.toAddMonoidHom (RiemannMasullo.integralAdeleDiagonal F S))

namespace RiemannMasullo

theorem adele_additive_quotient :
    let d := algebraMap F 𝔸[F]
    let q := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
    let q₀ := QuotientAddGroup.mk' (integralAdeleDiagonal F ∅).toAddMonoidHom.range
    Injective d ∧ IsClosed (Set.range d) ∧ IsDiscrete (Set.range d) ∧
    Exact d q ∧ IsOpenQuotientMap q ∧ CompactSpace (AQuot(F)) ∧ T2Space (AQuot(F)) ∧
    (∀ n : ℕ, 0 < n → Bijective (fun x : AQuot(F) ↦ n • x)) ∧
    (∃ e : IQuot(F, ∅) ≃ₜ+ (AQuot(F)), ∀ x, e (q₀ x) = q x.val) ∧
    (∀ (L : Type*) [Field L] [NumberField L] (σ : F →+* L),
      (∃! f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f) ∧
      ∀ f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f →
        ∃ (r : integralAdelesOutside F ∅ →+ integralAdelesOutside L ∅)
          (c : AQuot(F) →+ AQuot(L)) (c₀ : IQuot(F, ∅) →+ IQuot(L, ∅)),
          Continuous r ∧ Continuous c ∧ Continuous c₀ ∧ (∀ x, (r x).val = f x.val) ∧
          (∀ a, c (q a) = QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 L) L) (f a)) ∧
          ∀ x, c₀ (q₀ x) = QuotientAddGroup.mk' (integralAdeleDiagonal L ∅).toAddMonoidHom.range (r x)) := by sorry

end RiemannMasullo
