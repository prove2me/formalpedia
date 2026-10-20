-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_gray_wyner_sandwich
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.gray_wyner_sandwich
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:41:49.143375+00:00
-- url     : https://prove2.me/theorems/2d659cee-9fac-4014-b8c1-a6e9bdae1185
-- title:
--   §3.1 unnumbered: single-auxiliary Gray–Wyner outer region
-- statement:
--   Let $m\ge1$ and fix a normalized law of finite classical variables $X_1,\ldots,X_m$; write $X=(X_1,\ldots,X_m)$. Define $\mathcal R_c$ to contain the rates with $R_0\ge I(X;C)$ and $R_i\ge H(X_i\mid C)$ for some finite classical extension. Define $\mathcal R_q$ by $R_0\ge I(X;F_1\cdots F_m)$ and $R_i\ge H(X_i\mid F_i)$ for one joint finite quantum extension. Define $\mathcal R'_q$ using a single finite quantum extension $F$, with $R_0\ge I(X;F)$ and $R_i\ge H(X_i\mid F)$. All extensions have the same fixed source marginal. Then
--
--   $$
--   \mathcal R_c\subseteq\mathcal R_q\subseteq\mathcal R'_q,
--   \qquad
--   \mathcal R_c=\mathcal R'_q\ \Longrightarrow\ \mathcal R_c=\mathcal R_q.
--   $$
--
--   These are the coordinatewise upper regions, not merely their boundary tuples. This is the source's original entropic comparison; the cited operational characterizations are not additional theorem claims.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 6, §3.1 unnumbered: single-auxiliary Gray–Wyner outer region

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- §3.1, PDF pp.5–6: the region sandwich and its conditional equality consequence.
The printed F1 in the explanation of (4) is read as Fi, as required by (3). -/
theorem gray_wyner_sandwich {m : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hs : ∀ i, 0 < s i) (p : Law (Alphabet m s)) :
    classicalGW p ⊆ multiQuantumGW p ∧ multiQuantumGW p ⊆ singleQuantumGW p ∧
      (classicalGW p = singleQuantumGW p → classicalGW p = multiQuantumGW p) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
