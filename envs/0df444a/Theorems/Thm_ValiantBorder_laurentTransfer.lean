-- Prove2me | Theorems.Thm_ValiantBorder_laurentTransfer
-- name    : ValiantBorder.laurentTransfer
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-23T23:40:51.464696+00:00
-- url     : https://prove2.me/theorems/b1d86765-2866-42ee-8b59-ead18589f138
-- title:
--   Laurent polynomial constants suffice
-- statement:
--   Let $f$ have integer coefficients. If it has an $s$-gate approximation over a field of characteristic $p$, it has an $s$-gate approximation with Laurent polynomial constants over any algebraically closed field $K$ of characteristic $p$. The output has zero negative coefficients in the parameter and constant term $f$ over $K$.
-- source:
--   L. G. Valiant, Completeness classes in algebra, STOC 1979, https://doi.org/10.1145/800135.804419. P. Bürgisser, On Implications Between P-NP-Hypotheses, MFCS 2001, Conjecture 7.5, https://www3.math.tu-berlin.de/algebra/work/mfcs2001-contrib.pdf. Claude (Anthropic), VP ≠ VNP over every field, Appendix N, Lemma N.2 and Appendix Q (formal version), https://hexagonmath.org/2611.00954v1. https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Transfer.lean#L38-L45.

import Definitions.Def_VP_VNP_all_fields

theorem ValiantBorder.laurentTransfer.{u} {F : Type u} {K V : Type}
    [Field F] [Field K] [IsAlgClosed K] (p : ℕ) [CharP F p] [CharP K p]
    (f : MvPolynomial V ℤ) {s : ℕ}
    (h : Statement.Approximates (MvPolynomial.map (Int.castRingHom F) f) s) :
    ∃ q : MvPolynomial V (LaurentPolynomial K), Statement.Computes q s ∧
      ∀ d : V →₀ ℕ, (∀ i : ℤ, i < 0 → (MvPolynomial.coeff d q).coeff i = 0) ∧
        (MvPolynomial.coeff d q).coeff 0 =
          MvPolynomial.coeff d (MvPolynomial.map (Int.castRingHom K) f) := by sorry
