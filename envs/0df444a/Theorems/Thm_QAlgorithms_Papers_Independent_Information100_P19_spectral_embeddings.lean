-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_spectral_embeddings
-- name    : QAlgorithms.Papers.Independent.Information100.P19.spectral_embeddings
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:48:40.639052+00:00
-- url     : https://prove2.me/theorems/42ab2213-f6cb-4d3c-8f75-5480a2fb9382
-- title:
--   Proposition 4.3
-- statement:
--   For each partition $\lambda\vdash n$, form $\alpha_\lambda$ from successive increasing contiguous cycles in decreasing block-size order. The coefficient maps sending $[\lambda]$ respectively to $(\alpha_\lambda,\alpha_\lambda)$ and $(\alpha_\lambda,\alpha_\lambda^{-1})$ are injective and satisfy
--   $$\iota_+(I_n^{\rm psd})\subseteq I_n^{\rm sep},\qquad
--   \iota_\Gamma(I_n^{\rm psd})\subseteq I_n^{\rm sep}.$$
--   Their evaluations are $f(X)$ and $f(X^{\Gamma_B})$, respectively. The partial transpose acts on the second tensor factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 21, Proposition 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 4.3; arXiv:2609.29471v1, PDF pp.21. -/
theorem spectral_embeddings (n : ℕ) (hn : 1 ≤ n) :
    (∀ f ∈ psdCone n, embed false f ∈ sepCone n ∧ embed true f ∈ sepCone n) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.IsHermitian → ∀ f : Coeff n,
      tensorEval (embed false f) X = f.sum (fun l c => c *
        (l.val.map (fun k => powerTrace X k)).prod) ∧
      tensorEval (embed true f) X = f.sum (fun l c => c *
        (l.val.map (fun k => powerTrace (transposeB X) k)).prod)) ∧
    Function.Injective (@embed n false) ∧ Function.Injective (@embed n true) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
