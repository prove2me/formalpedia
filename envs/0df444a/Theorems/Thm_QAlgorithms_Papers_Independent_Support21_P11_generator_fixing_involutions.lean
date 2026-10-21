-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_generator_fixing_involutions
-- name    : QAlgorithms.Papers.Independent.Support21.P11.generator_fixing_involutions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:02:06.97903+00:00
-- url     : https://prove2.me/theorems/f1d0d7b3-e9e1-4c52-9303-b9b06c0281be
-- title:
--   Unique generator-fixing reversals and descent
-- statement:
--   Let $R$ be a commutative unital ring, $\omega$ an arbitrary $R$-valued sequence, and $n\ge1$. For $r\ge1$ and arbitrary $u_1,\ldots,u_r\in R$, let $\pi:W_n^{\mathrm{aff}}(\omega)\to W_{r,n}(\omega;u)$ be the canonical cyclotomic quotient map. Each algebra has a unique $R$-linear map $\ast$ fixing all its generators and satisfying
--
--   $$\ast^2=\mathrm{id},\qquad 1^\ast=1,\qquad (ab)^\ast=b^\ast a^\ast.$$
--
--   For the respective affine and cyclotomic maps,
--
--   $$\pi(z)^{\ast_{\mathrm{cyc}}}=\pi(z^{\ast_{\mathrm{aff}}})\qquad(z\in W_n^{\mathrm{aff}}).$$
--
--   Involutivity makes these maps bijective, so they are algebra anti-automorphisms. This supplies the structural reversals on the actual presented algebras and their compatibility under quotienting.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 2, §2, unnumbered involution

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Section 2, unnumbered structural result, PDF p.2. Existence and uniqueness
are asserted on both presented algebras, together with descent compatibility.
No involution is assumed on either algebra. -/
theorem generator_fixing_involutions (R : Type*) [CommRing R] (omega : ℕ → R)
    (n r : ℕ) (u : Fin r → R) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (∃! star : AffineBMW R omega n →ₗ[R] AffineBMW R omega n,
      IsGeneratorReversal n (affineS R omega n) (affineE R omega n)
        (affineX R omega n) star) ∧
    (∃! star : CyclotomicBMW R omega n r u →ₗ[R] CyclotomicBMW R omega n r u,
      IsGeneratorReversal n (cyclotomicS R omega n r u) (cyclotomicE R omega n r u)
        (cyclotomicX R omega n r u) star) ∧
    (∀ (aff : AffineBMW R omega n →ₗ[R] AffineBMW R omega n)
      (cyc : CyclotomicBMW R omega n r u →ₗ[R] CyclotomicBMW R omega n r u),
      IsGeneratorReversal n (affineS R omega n) (affineE R omega n)
        (affineX R omega n) aff →
      IsGeneratorReversal n (cyclotomicS R omega n r u) (cyclotomicE R omega n r u)
        (cyclotomicX R omega n r u) cyc →
      ∀ z : AffineBMW R omega n,
        cyc (cyclotomicMap R omega n r u z) = cyclotomicMap R omega n r u (aff z)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
