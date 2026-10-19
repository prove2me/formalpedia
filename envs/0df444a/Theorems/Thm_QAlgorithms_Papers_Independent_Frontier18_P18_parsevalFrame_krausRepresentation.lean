-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P18_parsevalFrame_krausRepresentation
-- name    : QAlgorithms.Papers.Independent.Frontier18.P18.parsevalFrame_krausRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:08:12.974404+00:00
-- url     : https://prove2.me/theorems/175d4d75-8856-40a4-aeda-7ef71b078173
-- title:
--   Lemma 2: frame transformation of Kraus representations
-- statement:
--   Let $\Phi:\mathfrak T(\mathcal H_A)\to\mathfrak T(\mathcal H_B)$ be a quantum channel with a finite or countable Kraus family $(V_k)_{k\in K}$. Thus $\sum_k V_k^*V_k=I$ strongly and $\Phi(X)=\sum_k V_kXV_k^*$ in trace norm for every trace-class $X$. Let $(|k\rangle)_{k\in K}$ be the canonical orthonormal basis of $\ell^2(K)$ and let $(\psi_i)_{i\in L}$ be any finite or countable Parseval frame in that space. Then
--
--   $$
--   W_i=\sum_{k\in K}\langle\psi_i|k\rangle V_k,
--   \qquad
--   \Phi(X)=\sum_{i\in L}W_iXW_i^*.
--   $$
--
--   The series defining each $W_i$ converges in operator norm. The new family satisfies $\sum_iW_i^*W_i=I$ strongly, and the channel series converges in trace norm. This allows redundant frames in place of an environment basis without changing the channel.
-- source:
--   Monotonicity of the Holevo quantity: a necessary condition for equality in terms of a channel and its applications, arXiv:1106.3297v6, PDF p. 9, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

noncomputable section

open Filter

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

-- Use the complex unital C-star calculus directly on bounded operators.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Frontier18.P18

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 2, PDF p.9: arbitrary finite or countable Parseval frames transform
Kraus representations by W_i = sum_k <psi_i|k> V_k. Each defining operator series
converges in operator norm, and the resulting channel series in trace norm. -/
theorem parsevalFrame_krausRepresentation
    {I J K L : Type} [Countable I] [Countable J] [Countable K] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (Phi : Matrix I I ℂ → Matrix J J ℂ)
    (hPhi : QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel Phi)
    (V : K → (Hilbert I →L[ℂ] Hilbert J))
    (hV : IsKrausRepresentation Phi V)
    (psi : L → Hilbert K) (hFrame : IsParsevalFrame psi) :
    (∀ i : L, Summable (fun k => (inner ℂ (psi i) (lp.single 2 k 1)) • V k)) ∧
    IsKrausRepresentation Phi (frameKrausTransform V psi) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P18

end
