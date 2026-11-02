-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d4_uv_entropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d4_uv_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:58:38.366446+00:00
-- url     : https://prove2.me/theorems/16d4fe23-386c-41aa-8bac-902df9d42dc2
-- title:
--   Finite UV-subtracted D4 reduced action
-- statement:
--   Fix positive D4 coupling $\lambda$ and compactification radius $R_4$, and an integer $N_c\ge1$, with $\alpha'=1$. Put $U_0=4\pi\lambda/(9R_4^2)$, $R_{\mathrm{curv}}^3=\pi\lambda$, $G_N^{(10)}=8\pi^6\lambda^2/N_c^2$, and $K=\pi^3R_{\mathrm{curv}}^6U_0R_4/(2G_N^{(10)})$. For any regular physical disk or cylinder inverse profile $r(z)$ with boundary radius $\rho>0$ and endpoint depth $b$, use the actual reduced action
--
--   $$
--   S(a)=K\int_a^b\frac{r(z)^2}{z^3}\sqrt{1+z(1-z^3)r'(z)^2}\,dz.
--   $$
--
--   There exists a finite real remainder $S_{\mathrm{finite}}(0)$ such that
--
--   $$
--   S(a)-K\left[\frac{\rho^2}{2a^2}-\frac{3}{2a}+\frac{\log a}{8\rho^2}\right]
--   \longrightarrow S_{\mathrm{finite}}(0)\qquad(a\to0^+).
--   $$
--
--   This is the UV subtraction for the chosen reduced functional. It does not derive its disputed absolute geometric normalization or assert physical validity at arbitrarily high field-theory cutoff.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 18, (4.17)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF pp.18--19, (4.17): finite UV remainder of the actual reduced D4 action
for either regular topology. K is exactly the chosen reduced-regulatedAction prefactor;
no assertion repairs the induced-metric normalization. -/
theorem d4_uv_entropy (P : D4Parameters) (N : ℕ) (hN : 0 < N)
    (rho b : ℝ) (r : ℝ → ℝ) (hr : IsProfile .d4 rho b r) :
    ∃ finite : ℝ,
      Tendsto (fun a => d4Entropy P N r a b - d4Prefactor P N * uv .d4 rho a)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds finite) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
