-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P15_closeExtensions
-- name    : QAlgorithms.Papers.Independent.Frontier18.P15.closeExtensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:05:16.255095+00:00
-- url     : https://prove2.me/theorems/61f6124c-522a-4341-aed9-9f704a84e24f
-- title:
--   Close states admit close extensions on the same space
-- statement:
--   Let $\rho^A$ and $\sigma^A$ be density operators on a finite system $A$, let $\epsilon\ge0$, and suppose $\|\rho^A-\sigma^A\|_1\le\epsilon$. For every density operator $\sigma^{AB}$ on a finite extension $A\otimes B$ satisfying $\operatorname{Tr}_B\sigma^{AB}=\sigma^A$, there is a density operator $\rho^{AB}$ on that same space such that
--
--   $$
--   \operatorname{Tr}_B\rho^{AB}=\rho^A,\qquad \|\rho^{AB}-\sigma^{AB}\|_1\le2\sqrt{\epsilon}.
--   $$
--
--   Both systems have positive dimension; a null extension is one dimensional. This result transfers trace-norm closeness to a prescribed extension, without changing the extension space.
-- source:
--   A Resource Framework for Quantum Shannon Theory, arXiv:quant-ph/0512015v1, PDF p. 9, Lemma 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P15

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P15

/-- Lemma 2.2, PDF p.9: a prescribed extension of sigma has a nearby extension of rho
on the same A × B space. The printed constant is 2 sqrt(epsilon). -/
theorem closeExtensions (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (rho sigma : Matrix (Fin a) (Fin a) ℂ)
    (sigmaExt : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hext : IsDensityMatrix sigmaExt) (hmarginal : traceRight sigmaExt = sigma)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hclose : traceNorm (rho - sigma) ≤ epsilon) :
    ∃ rhoExt : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      IsDensityMatrix rhoExt ∧ traceRight rhoExt = rho ∧
        traceNorm (rhoExt - sigmaExt) ≤ 2 * Real.sqrt epsilon := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P15

end
