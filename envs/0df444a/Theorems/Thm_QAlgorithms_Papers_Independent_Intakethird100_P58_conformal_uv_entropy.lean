-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_conformal_uv_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.conformal_uv_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:55:56.493554+00:00
-- url     : https://prove2.me/theorems/aa06f30c-2cda-4bc7-827d-79d184d00124
-- title:
--   Conformal UV divergences and the finite dimensionless remainder
-- statement:
--   For the regular conformal disk profiles just described, let $l>0$ be the translation-invariant cylinder length, $N_c\ge1$ the number of colors, $R>0$ the boundary radius, and $b>0$ the axis depth. There is a finite dimensionless number $\widetilde\gamma$, independent of $R,l,N_c$ and the regular disk representation, such that the actual reduced action
--
--   $$
--   S(a)=\frac{4N_c^2l}{15\pi}\int_a^b\frac{r(z)}{z^3}\sqrt{1+r'(z)^2}\,dz
--   $$
--
--   satisfies, as $a\to0^+$,
--
--   $$
--   S(a)-\frac{2N_c^2}{15\pi}\left(\frac{lR}{a^2}+\frac{l}{4R}\log\frac aR\right)
--   \longrightarrow-\frac{4N_c^2l}{15\pi R}\widetilde\gamma.
--   $$
--
--   The integral includes the side surface only. This isolates a finite conformal remainder without promoting the numerical report $0.305$ to an exact equality.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 9, (3.13)–(3.15)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF p.9, (3.15): actual conformal profile integral minus both UV terms
has a finite limit. The dimensionless remainder is independent of R,l,N.
The numerical estimate 0.305 is not promoted to an exact equality. -/
theorem conformal_uv_entropy :
    ∃ gamma : ℝ, ∀ (R b : ℝ) (r : ℝ → ℝ), IsDisk .conformal R b r →
      ∀ (l : ℝ), 0 < l → ∀ N : ℕ, 0 < N →
        Tendsto (fun a => conformalEntropy N l r a b -
          4 * (N : ℝ) ^ 2 * l / (15 * Real.pi) * uv .conformal R a)
          (nhdsWithin (0 : ℝ) (Ioi 0))
          (nhds (-4 * (N : ℝ) ^ 2 * l / (15 * Real.pi * R) * gamma)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
