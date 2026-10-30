-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_tsallis_subadditive_not_firmlySubadditive
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.tsallis_subadditive_not_firmlySubadditive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:55:39.856859+00:00
-- url     : https://prove2.me/theorems/3d50e83d-c05b-4469-b83f-32a1d290e583
-- title:
--   Source-reported subadditive Tsallis entropies that fail FSA
-- statement:
--   For a real parameter $q>0$ with $q\ne1$, define $S_{T,q}(\rho)=(\operatorname{Tr}\rho^q-1)/(1-q)$, using the von Neumann value at $q=1$. Let $I_{T,q}$ and $\chi_{T,q}$ be the associated mutual information and measurement Holevo quantity, and let $\delta_{T,q}(P_a,b)=I_{T,q}(a:b)-\chi_{T,q}(P_a,b)$.
--
--   The paper reports the following interval claim, based on numerical examples:
--
--   $$
--   \forall q\in(2+1/200,\,3-1/200),\qquad
--   S_{T,q}\text{ is subadditive},\quad
--   \exists\rho_{ab},P_a:\ \delta_{T,q}(P_a,b)<0.
--   $$
--
--   The state is a normalized density on some finite positive bipartite dimensions, and $P_a$ is a finite POVM. The dimensions and witness may depend on $q$.
--
--   This is the source’s claimed separation between SA and FSA. The paper prints neither witness matrices nor a certificate verifying the entire continuous interval; the formal statement records that source-reported claim.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 4, §VI and Figure 1, unnumbered: subadditive Tsallis entropies can fail FSA

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.4, §VI and Fig.1: source-reported numerical interval claim, not an
analytically certified search. For each q the witness may depend on q; no dimensions
or explicit witness matrices are invented. The open interval is exactly (2.005,2.995). -/
theorem tsallis_subadditive_not_firmlySubadditive :
    ∀ q : ℝ, 2 + (1 : ℝ) / 200 < q → q < 3 - (1 : ℝ) / 200 →
      SubadditiveEntropy (tsallisEntropy q) ∧
      (∃ (a b m : ℕ), 0 < a ∧ 0 < b ∧ 0 < m ∧
        ∃ (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
          (P : Fin m → Matrix (Fin a) (Fin a) ℂ),
          IsDensityMatrix rho ∧ IsPOVM P ∧ povmSpecificDiscord (tsallisEntropy q) rho P < 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end
