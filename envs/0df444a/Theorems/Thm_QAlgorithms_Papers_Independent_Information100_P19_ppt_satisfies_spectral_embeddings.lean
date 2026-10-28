-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_ppt_satisfies_spectral_embeddings
-- name    : QAlgorithms.Papers.Independent.Information100.P19.ppt_satisfies_spectral_embeddings
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:05:01.899995+00:00
-- url     : https://prove2.me/theorems/8ef5e321-8b29-4c29-9039-1565676bf697
-- title:
--   §6.4 unnumbered: embedded spectral tests cannot detect PPT entanglement
-- statement:
--   For every PSD-valid homogeneous one-matrix inequality $f$ and every bipartite PSD operator $X$ whose partial transpose on B is also PSD,
--   $$\operatorname{Tr}_{\iota_+(f)}X\ge0,\qquad\operatorname{Tr}_{\iota_\Gamma(f)}X\ge0.$$
--   No trace normalization is needed. Consequently, inequalities from either spectral embedding cannot detect PPT entanglement.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 44, §6.4 unnumbered: embedded spectral tests cannot detect PPT entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §6.4 unnumbered: embedded spectral tests cannot detect PPT entanglement; arXiv:2609.29471v1, PDF pp.44. -/
theorem ppt_satisfies_spectral_embeddings (n : ℕ) (hn : 1≤n) (f : Coeff n) (hf : f∈psdCone n)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (X : Bip a b)
    (hX : X.PosSemidef) (hPPT : (transposeB X).PosSemidef) :
    0≤tensorEval (embed false f) X ∧ 0≤tensorEval (embed true f) X := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
